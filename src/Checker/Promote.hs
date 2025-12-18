module Checker.Promote where

import Control.Monad
import Control.Monad.Reader

import Checker.Monad
import Checker.Types hiding (trace)
import Checker.Utils
import Printer
import Syntax

import GHC.Stack

{--

Promotion
=========

Promotion is doing (for now) several things:

 - The occurs check: making sure we're not attempting to compute an
   infinite type
 - Unshifting any type variables by the shift on UV, failing if a
   variable would be captured
 - Unshifting any unsolved unification variables; if they can't be
   unshifted far enough, generating a fresh uvar to take their role

If that much ever works, I'll then return to the levels question, as
I suspect that the better way to handle levels is via promotion rather
than having level references

--}

promote :: MonadCheck m => UVar -> Ty -> m (Maybe Ty)
promote uv = promoteN uv 0

promoteN :: MonadCheck m => UVar -> Int -> Ty -> m (Maybe Ty)
promoteN v@(UV n l' _ _) m t@(TVar i s) =
  do kb <- asks ((!! i) . kctxt)
     case kb of
       KBVar _ l
         | l' < l -> do trace $ "8 incoming unification failure: unable to promote " ++ show v ++ " to " ++ show t
                        return Nothing
         | i < m -> return (Just t)
         | i >= n -> return (Just $ TVar (i - n) s)
         | otherwise -> return Nothing
       -- Really don't think this should be possible...
       KBDefn _ u -> promoteN v m u
promoteN v@(UV n l (Goal (_, r)) _) m t@(TUnif v'@(UV n' l' (Goal (uvar', r')) k'))
  | r == r' = return Nothing -- Occurs check
  | otherwise =
    do mt <- readRef r'
       case mt of
         Just t' -> promoteN v m (shiftTN 0 n' t')
         Nothing
           | n' < m ->
             do trace $ "promoteN 1: " ++ show n' ++ " < " ++ show m
                return (Just t)
           | n' >= m + n && l >= l' ->
             do trace "promoteN 2"
                return (Just $ TUnif (v' { uvShift = n' - n }))
           | otherwise ->
             do trace "promoteN 3"
                r'' <- newRef Nothing
                uvar'' <- fresh uvar'
                let newT n = TUnif (UV n l (Goal (uvar'', r'')) k')
                writeRef r' (Just (newT ((m + n) - n')))
                return (Just (newT m))
promoteN v _ TFun = return (Just TFun)
promoteN v n (TThen p t) = liftM2 TThen <$> promoteP v n p <*> promoteN v n t
promoteN v n (TForall s (Just k) t) = liftM (TForall s (Just k)) <$> (atLevel 0 $ bindTy k $ promoteN v (n + 1) t)
promoteN v n (TForall s Nothing t) = error "can't promote unkinded forall"
promoteN v n (TLam s (Just k) t) = liftM (TLam s (Just k)) <$> (atLevel 0 $ bindTy k $ promoteN v (n + 1) t)
promoteN v n (TLam s Nothing t) = error "can't promote unkinded lambda"
promoteN v n (TApp t u) = liftM2 TApp <$> promoteN v n t <*> promoteN v n u
promoteN _ _ (TLab s) = return (Just (TLab s))
promoteN v n (TSing t) = liftM TSing <$> promoteN v n t
promoteN v n (TLabeled l t) = liftM2 TLabeled <$> promoteN v n l <*> promoteN v n t
promoteN v n (TRow ts) = liftM TRow . sequence <$> mapM (promoteN v n) ts
promoteN v n (TConApp k t) = liftM (TConApp k) <$> promoteN v n t
promoteN v n TString = return (Just TString)
promoteN v n (TMapFun t) = liftM TMapFun <$> promoteN v n t
promoteN v n (TCompl y z) = liftM2 TCompl <$> promoteN v n y <*> promoteN v n z
promoteN v@(UV n l _ _) m (TInst is t) = liftM2 TInst <$> promoteIs is <*> promoteN v m t
  where promoteIs :: MonadCheck m => Insts -> m (Maybe Insts)
        promoteIs is@(Unknown n' g@(Goal (s, r))) =
          do mis <- readRef r
             case mis of
               Just is -> promoteIs (shiftIsV [] 0 n' is)
               Nothing
                 | n' >= n   -> return (Just $ Unknown (n' - n) g)
                 | otherwise -> do r' <- newRef Nothing
                                   s' <- fresh s
                                   let newIs n = Unknown n (Goal (s', r'))
                                   writeRef r (Just (newIs (n - n')))
                                   return (Just (newIs 0))
        promoteIs (Known is) = liftM Known . sequence <$> mapM promoteI is
        promoteI :: MonadCheck m => Inst -> m (Maybe Inst)
        promoteI (TyArg t) = liftM TyArg <$> promoteN v n t
        promoteI i@(PrArg v) = return (Just i)
promoteN v n (TMapArg f) = liftM TMapArg <$> promoteN v n f
promoteN v n t = error $ "promote: missing " ++ show t

promoteP :: MonadCheck m => UVar -> Int -> Pred -> m (Maybe Pred)
promoteP v n (PEq t u) = liftM2 PEq <$> promoteN v n t <*> promoteN v n u
promoteP v n (PLeq y z) = liftM2 PLeq <$> promoteN v n y <*> promoteN v n z
promoteP v n (PPlus x y z) = liftM3 PPlus <$> promoteN v n x <*> promoteN v n y <*> promoteN v n z

-- TODO: the Evid returned here is always and only VEqRefl... why needed?
solveUV :: (HasCallStack, MonadCheck m) => UVar -> Ty -> m (Maybe Evid)
solveUV v t =
  do k <- kindOf t
     -- next line is arguably wrong: should just make unification fail, not immediately signal a type error
     expectK t k (uvKind v)
     let tString = renderString (ppr t)
     --
     mt' <- promote v t
     case mt' of
       Nothing ->
        do trace $ unwords ["9 incoming unification failure: unable to promote ", show t, " to match ", show v ]
           return Nothing
       Just t' ->
         do trace ("1 promoted " ++ tString ++ " to " ++ renderString (ppr t'))
            trace ("1 instantiating " ++ goalName (uvGoal v) ++ "@" ++ show (uvLevel v) ++ " to " ++ renderString (ppr  t')) --  renderString (ppr t'))
            writeRef (goalRef (uvGoal v)) (Just t')
            return (Just VEqRefl)