module Checker.Normalize where

import Control.Monad.Reader
import Data.Bifunctor (first)
import Data.List
import Data.Maybe

import Checker.Monad
import Checker.Utils
import Syntax

import GHC.Stack


class HasTyVars t where
  subst :: MonadRef m => Int -> Ty -> t -> m t

instance HasTyVars Ty where
  subst j t u@(TVar i _)
    | j == i = return t
    | otherwise = return u
  subst v t u@(TUnif (UV n _ (Goal (y, r)) k)) =
    do mt <- readRef r
       case mt of
         Nothing -> return u
         Just u  -> do u' <- subst v t (shiftTN 0 n u)
                       -- TODO: This should be handled by promotion as well
                       writeRef r (Just (shiftTN 0 (negate n) u'))
                       return u'
  subst v t TFun = return TFun
  subst v t (TThen p u) = TThen <$> subst v t p <*> subst v t u
  subst v t (TForall w k u) = TForall w k <$> subst (v + 1) (shiftT 0 t) u
  subst v t (TLam w k u) = TLam w k <$> subst (v + 1) (shiftT 0 t) u
  subst v t (TApp u0 u1) =
    TApp <$> subst v t u0 <*> subst v t u1
  subst v t u@(TLab _) = return u
  subst v t (TSing u) = TSing <$> subst v t u
  subst v t (TLabeled l u) = TLabeled <$> subst v t l <*> subst v t u
  subst v t (TRow us) = TRow <$> mapM (subst v t) us
  subst v t (TConApp k u) = TConApp k <$> subst v t u
  subst v t (TCompl y x) = TCompl <$> subst v t y <*> subst v t x
  subst v t (TInst (Known is) u) = TInst <$> (Known <$> mapM substI is) <*> subst v t u where
    substI (TyArg u) = TyArg <$> subst v t u
    substI (PrArg v) = return (PrArg v)
  subst v t (TInst i@(Unknown n (Goal (_, r))) u) =
    do minst <- readRef r
       case minst of
         Nothing -> TInst i <$> subst v t u
         Just is -> subst v t (TInst (shiftIsV [] 0 n is) u)
  subst v t (TMapFun f) = TMapFun <$> subst v t f
  subst v t (TMapArg f) = TMapArg <$> subst v t f
  subst v t u = error $ "internal: subst " ++ show v ++ " (" ++ show t ++ ") (" ++ show u ++")"

instance HasTyVars Pred where
  subst v t (PEq u u') = PEq <$> subst v t u <*> subst v t u'
  subst v t (PLeq y z) = PLeq <$> subst v t y <*> subst v t z
  subst v t (PPlus x y z) = PPlus <$> subst v t x <*> subst v t y <*> subst v t z

normalize' :: (HasCallStack, MonadCheck m) => [Eqn] -> Ty -> m (Ty, Evid)
normalize' eqns t =
  do (u, q) <- normalize eqns t
     theKCtxt <- asks kctxt
     case q of
       VEqRefl -> return (u, q)
       _       -> do trace $ "normalize (" ++ show t ++ ") -->* (" ++ show u ++ ") in " ++ show theKCtxt
                     return (u, q)

normalize :: (HasCallStack, MonadCheck m) => [Eqn] -> Ty -> m (Ty, Evid)
normalize eqns t
  | Just (u, v) <- lookup t eqns =
    do (u', q) <- normalize eqns u
       return (u', VEqTrans v q)
normalize eqns t@(TVar i _) =
  do kb <- asks ((!! i) . kctxt)
     case kb of
       KBVar _ _ -> return (t, VEqRefl)
       KBDefn _ def -> do (t', q) <- normalize eqns (shiftTN 0 (i + 1) def)
                          return (t', VEqTrans VEqDefn q)
normalize eqns t0@(TApp (TLam x (Just k) t) u) =
  do t1 <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 u) t
     (t2, q) <- normalize eqns t1
     return (t2, VEqTrans VEqBeta q)
normalize eqns (TApp (TConApp Pi r) t) =
  do (t1, q) <- normalize eqns (TConApp Pi (TApp (TMapArg r) t))  -- To do: check kinding
     return (t1, VEqTrans (VEqLiftTyCon Pi) q)
normalize eqns (TApp (TConApp Sigma r) t) =
  do (t1, q) <- normalize eqns (TConApp Sigma (TApp (TMapArg r) t))
     return (t1, VEqTrans (VEqLiftTyCon Sigma) q)
normalize eqns (TApp (TMapFun f) (TRow es))
  | Just ls <- mapM label es, Just ts <- mapM labeled es =
    do (t, q) <- normalize eqns (TRow (zipWith TLabeled ls (map (TApp f) ts)))
       return (t, VEqTrans VEqMap q)
-- The next rule implements `map id == id`
normalize eqns (TApp (TMapFun f) z)
  | TLam _ k (TVar 0 _) <- f =
    do (z, q) <- normalize eqns z
       return (z, VEqTrans VEqMapId q)
-- The following rules (attempt to) implement `map f . map g == map (f . g)`.
-- The need for special cases arises from our various ways to represent type
-- functions: they're not all `TLam`. There are probably some cases missing: in
-- particular, I see nothing about nested maps.
normalize eqns (TApp (TMapFun (TLam _ _ f)) (TApp (TMapFun (TLam v k g)) z)) =
  do f' <- subst 0 g f
     (t, q) <- normalize eqns (TApp (TMapFun (TLam v k f')) z)
     return (t, VEqTrans VEqMapCompose q)
normalize eqns (TApp (TMapFun (TLam v (Just (KFun KType KType)) f)) (TApp (TMapFun TFun) z)) =
  do f' <- subst 0 (TApp TFun (TVar 0 v)) f
     (t, q) <- normalize eqns (TApp (TMapFun (TLam v (Just KType) f')) z)
     return (t, VEqTrans VEqMapCompose q)
normalize eqns (TApp (TMapFun TFun) (TApp (TMapFun (TLam v k f)) z)) =
  do (t, q) <- normalize eqns (TApp (TMapFun (TLam v k (TApp TFun f))) z)
     return (t, VEqTrans VEqMapCompose q)
normalize eqns (TApp (TMapArg (TRow es)) t)
  | Just ls <- mapM label es, Just fs <- mapM labeled es =
    do (t, q) <- normalize eqns (TRow (zipWith TLabeled ls (map (`TApp` t) fs)))
       return (t, VEqTrans VEqMapCompose q)
normalize eqns (TMapArg z) =
    do k <- kindOf z
       case k of
         KRow (KFun k1 k2) -> return (TLam "X" (Just k1) (TApp (TMapFun (TLam "Y" (Just (KFun k1 k2)) (TApp (TVar 0 "Y") (TVar 1 "X")))) (shiftTN 0 1 z)), VEqDefn)
         _ -> fail ("normalize: ill-kinded " ++ show (TMapArg z))
normalize eqns (TApp t1 t2) =
  do (t1', q1) <- normalize eqns t1
     q1' <- flattenV q1
     case q1' of
       VEqRefl -> do (t2', q2) <- normalize eqns t2
                     return (TApp t1 t2', VEqApp VEqRefl q2)
       _ -> do (t', q) <- normalize eqns (TApp t1' t2)
               return (t', VEqTrans (VEqApp q1 VEqRefl) q)
normalize eqns (TLabeled tl te) =
  do (tl', ql) <- normalize eqns tl
     (te', qe) <- normalize eqns te
     return (TLabeled tl' te', VEqLabeled ql qe)
normalize eqns (TRow ts) =
  do (ts', qs) <- unzip <$> mapM (normalize eqns) ts
     case mapM splitConcreteLabel ts' of
       Just ps ->
         let ps' = sortOn (fst . fst) (zip ps qs)
             is  = [fromJust (elemIndex i (map (fst . fst) ps')) | i <- map fst ps] in
         return (TRow (map (uncurry (TLabeled . TLab)) (map fst ps')), VEqRowPermute is `VEqTrans` VEqRow (map snd ps'))
       Nothing ->
         return (TRow ts', VEqRow qs)
normalize eqns (TConApp Sigma z) =
  do (z', q) <- normalize eqns z
     k <- kindOf z'
     case k of
       KRow (KRow k') ->
         do (z'', q') <- normalize eqns (TApp (TMapFun (TLam "x" (Just k) (TConApp Sigma (TVar 0 "x")))) z')
            return (z'', VEqTrans q q')
       _ -> return (TConApp Sigma z', VEqCon Sigma q)
normalize eqns (TConApp Pi z) =
  do (z', q) <- normalize eqns z
     k <- kindOf z'
     case k of
       KRow (KRow k') ->
         do (z'', q') <- normalize eqns (TApp (TMapFun (TLam "x" (Just k) (TConApp Pi (TVar 0 "x")))) z')
            return (z'', VEqTrans q q')
       _ -> return (TConApp Pi z', VEqCon Pi q)
normalize eqns (TConApp Mu z) =
  do (z', q) <- normalize eqns z
     return (TConApp Mu z', VEqCon Mu q)
normalize eqns (TForall x (Just k) t) =
  do (t', q) <- bindTy k (normalize eqns t)
     return (TForall x (Just k) t', VEqForall q) -- probably should be a congruence rule mentioned around here.... :)
normalize eqns (TLam x (Just k) t) =
  do (t', q) <- bindTy k (normalize eqns t)
     return (TLam x (Just k) t', VEqLambda q)
normalize eqns (TMapFun t) =
  do (t', q) <- normalize eqns t
     return (TMapFun t', q)
normalize eqns (TCompl x y) =
  do (x', q) <- normalize eqns x
     (y', q') <- normalize eqns y
     case (x', y') of
       (TRow xs, TRow ys)
         | Just xls <- mapM label xs
         , Just yls <- mapM label ys
         , all (`elem` xls) yls -> return (TRow [TLabeled l t | TLabeled l t <- xs, l `notElem` yls], VEqTrans (VEqComplCong q q') VEqCompl)
       _ -> return (TCompl x' y', VEqComplCong q q')
normalize eqns (TInst ig@(Unknown n (Goal (s, r))) t) =
  do minsts <- readRef r
     case minsts of
       Nothing -> first (TInst ig) <$> normalize eqns t
       Just is -> normalize eqns (TInst is t)
normalize eqns (TInst (Known []) t) =
  normalize eqns t
normalize eqns (TInst (Known is) t) =
  do is' <- mapM normI is
     first (TInst (Known (map fst is'))) <$> normalize eqns t  -- TODO: should probably do something with the evidence here, but what. Not sure this case should even really be possible...
  where normI (TyArg t) = first TyArg <$> normalize eqns t
        normI (PrArg v) =
          return (PrArg v, VEqRefl)
normalize eqns (TThen p t) =
  do p' <- normalizeP eqns p
     (t', q) <- normalize eqns t
     return (TThen p' t', VEqThen VEqRefl q)
-- TODO: remaining homomorphic cases
normalize eqns t = return (t, VEqRefl)

normalizeP :: MonadCheck m => [Eqn] -> Pred -> m Pred -- no evidence structure for predicate equality yet soooo....
normalizeP eqns (PLeq x y) = PLeq <$> (fst <$> normalize eqns x) <*> (fst <$> normalize eqns y)
normalizeP eqns (PPlus x y z) = PPlus <$> (fst <$> normalize eqns x) <*> (fst <$> normalize eqns y) <*> (fst <$> normalize eqns z)
normalizeP eqns (PEq t u) = PEq <$> (fst <$> normalize' eqns t) <*> (fst <$> normalize' eqns u)
