{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Checker.Unify (module Checker.Unify) where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (first, second)
import Data.Dynamic
import Data.IORef
import Data.List (partition)
import Data.Maybe (isNothing)

import Checker.Monad
import Checker.Types
import Syntax

import GHC.Stack

data Update where
  U :: IORef a -> a -> Update

perform :: MonadIO m => Update -> m ()
perform (U ref val) = liftIO $ writeIORef ref val

type US = Maybe [Dynamic]
type UW = ([Update], [(Pred, IORef (Maybe Evid))])
newtype UnifyM a = UM { runUnifyM :: StateT US (WriterT UW CheckM) a }
  deriving (Functor, Applicative, Monad, MonadWriter UW, MonadError Error, MonadIO, MonadState US)

liftC :: CheckM a -> UnifyM a
liftC = UM . lift . lift

instance MonadRef UnifyM where
  newRef v = UM $ StateT $ \checking -> WriterT (body checking) where
    body Nothing = do r <- liftIO (newIORef v)
                      return ((r, Nothing), ([], []))
    body (Just rs) = do r <- liftIO (newIORef v)
                        return ((r, Just (toDyn r : rs)), ([], []))
  readRef = liftIO . readIORef
  writeRef r v =
    do v' <- readRef r
       tell ([U r v'], [])
       liftIO (writeIORef r v)

instance MonadReader TCIn UnifyM where
  ask = UM (lift (lift ask))
  local f r = UM $ StateT $ \checking -> WriterT $ local f (runWriterT (runStateT (runUnifyM r) checking))

instance MonadCheck UnifyM where
  bindTy k m = UM $ StateT $ \checking -> WriterT $ bindTy k (runWriterT $ runStateT (runUnifyM m) checking)
  defineTy k t m = UM $ StateT $ \checking -> WriterT $ defineTy k t (runWriterT $ runStateT (runUnifyM m) checking)
  bind t m = UM $ StateT $ \checking -> WriterT $ bind t (runWriterT $ runStateT (runUnifyM m) checking)
  assume g m = UM $ StateT $ \checking -> WriterT $ assume g (runWriterT $ runStateT (runUnifyM m) checking)
  require p r = tell ([], [(p, r)])
  fresh = UM . lift . lift . fresh

canUpdate :: Typeable a => IORef a -> UnifyM Bool
canUpdate r = UM (StateT $ \checking -> WriterT (body checking)) where
  body Nothing = return ((True, Nothing), ([], []))
  body (Just rs) = return ((any ok rs, Just rs), ([], []))
  ok dr = case fromDynamic dr of
            Just r' -> r == r'
            Nothing -> False

{--

Unification variables and shifts
================================

The significant source of complexity in the new version of type inference is the
interaction of unification variables and shifts.

Generally, shifts do not cause so much of a problem (at least, so long as you
are ignoring efficiency): when you go under a type binder, you shift the term
bindings and predicate bindings accordingly.

However, it is not so easy to shift a unification variable, because we don't yet
know what type that unification variable will take on. So unification variables
"store delayed shifts": a unification variable `TUnif n ref k` should have its
variables shifted up by `n`.

For unification, this means that when we attempt to unify `TUnif n ref k` with
`t`, we need to update `ref` with a type u *such that* `shiftTN 0 n u` produces
`t`. We do this by essentially *unshifting* `t`.

Of course, the trick is that *unshifting* a type can fail! For example, this
should happen if an existentially bound type variable were to escape its
context. (Minor quibble: we don't have existentially bound type variables... but
you get my point). At the moment, this results in an unpleasant error message,
because `shiftTN` is not designed to be able to fail.

TODO: are there legitimate programs (ill-typed but not triggering a compiler
bug) which ought to trigger this behavior? (Explore encodings of existential
types). How bad are the error messages?

--}

unify, check, unifyProductive :: HasCallStack => Ty -> Ty -> CheckM (Maybe Evid)
unify actual expected =
  do (result, (undoes, preds)) <- runWriterT $ evalStateT (runUnifyM $ unify' actual expected) Nothing
     if isNothing result
     then mapM_ perform undoes
     else mapM_ (uncurry require) preds
     return result

check actual expected =
  do (result, (undoes, preds)) <- runWriterT $ evalStateT (runUnifyM $ unify' actual expected) (Just [])
     if isNothing result
     then mapM_ perform undoes
     else mapM_ (uncurry require) preds
     return result

unifyProductive actual expected =
  do (result, (undoes, preds)) <- runWriterT $ evalStateT (runUnifyM $ unify' actual expected) Nothing
     if isNothing result || not (productive result)
     then do mapM_ perform undoes
             return Nothing
     else do mapM_ (uncurry require) preds
             return result
  where productive (Just (VVar _)) = False
        productive _               = True

checking :: UnifyM t -> UnifyM t
checking m =
  do s <- get
     put (Just [])
     x <- m
     put s
     return x

refine :: UnifyM (Maybe Evid) -> UnifyM (Maybe Evid)
refine m =
  do s <- get
     case s of
       Nothing -> m
       Just _  -> return Nothing

requireEq :: Ty -> Ty -> UnifyM (Maybe Evid)
requireEq t u =
  do v <- newRef Nothing
     require (PEq t u) v
     return (Just (VGoal (Goal ("q", v))))

unify' :: HasCallStack => Ty -> Ty -> UnifyM (Maybe Evid)
unify' actual expected =
  do trace ("(" ++ show actual ++ ") ~ (" ++ show expected ++ ")")
     (actual', q) <- normalize actual
     (expected', q') <- normalize expected -- TODO: do we need to renormalize each time around?
     let f = case q of
               VRefl -> id
               _     -> VTrans q
         f' = case q' of
               VRefl -> id
               _     -> VTrans (VEqSym q')
     ((f' . f) <$>) <$> unify0 actual' expected'


-- This function handles unification cases `t ~ u` where `u` starts with some
-- instantiation variables. If `t` start with instantiation variables instead,
-- pass it as `u` but pass `flip unify` as the third argument.
unifyInstantiating :: Ty -> Ty -> (Ty -> Ty -> UnifyM (Maybe Evid)) -> UnifyM (Maybe Evid)
unifyInstantiating t u unify
  | Just matches <- match (reverse uis) (reverse (take (length tqs - nuqs) tqs)) =
      do t' <- instantiates (reverse matches) t
         unify t' u'
  | otherwise =
      do trace $ "7 incoming unification failure: (" ++ show t ++ ") (" ++ show u ++ ")"
         return Nothing
  where (tqs, _) = quants t
        (uis, u') = insts u
        nuqs      = length (fst (quants u'))

        -- match needs its arguments **reversed** from their appearance in the type
        match :: [Insts] -> [Quant] -> Maybe [Either (Ty, Kind) (Goal [Inst], [Quant])]
        match [] [] = return []
        match [Unknown g] qs = return [Right (g, reverse qs)]
        match (Unknown g : is@(Known _ : _)) qs = (Right (g, reverse thens) :) <$> match is rest where
          isThen (QuThen _) = True
          isThen _          = False
          (thens, rest) = partition isThen qs
        match (Unknown g : is@(Unknown _ : _)) qs =  -- still think this shouldn't be possible, clearly I don't understand my own code
          (Right (g, []) :) <$> match is qs
        match (Known is : is') qs =
          do (ms, qs') <- matchKnown is qs
             (ms ++) <$> match is' qs'
          where matchKnown [] qs = return ([], qs)
                matchKnown (TyArg t : is) (QuForall _ k : qs) = (first (Left (t, k) :)) <$> matchKnown is qs
                matchKnown (PrArg _ : _) _ = Nothing
                matchKnown _ [] = Nothing
        match is qs = error $ "ruh-roh: " ++ show is ++ " " ++ show qs

        -- Need to write function to apply list of instantiations derived from
        -- `match` above. Problem is (a) need to work outside in, but (b)
        -- instantiation (as demonstrated below) needs to operate on the
        -- remainder of the type, which has been somewhat disassembled
        --
        -- Approach: go back to original type, using list of insts to guide
        -- instantiation??
        instantiates :: [Either (Ty, Kind) (Goal [Inst], [Quant])] -> Ty -> UnifyM Ty
        instantiates [] t = return t
        instantiates (Left (u, _) : is) (TForall x k t) =
            do t' <- subst 0 (shiftTN 0 1 u) t
               instantiates is (shiftTN 0 (-1) t')
        instantiates (Right (Goal (_, r), qs) : is) t =
          do (is', t') <- instantiate (length qs) t
             writeRef r (Just is')
             instantiates is t'

        instantiate :: Int -> Ty -> UnifyM ([Inst], Ty)
        instantiate 0 t = return ([], t)
        instantiate n (TForall x (Just k) t) =
          do u <- typeGoal' x k
             t' <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 u) t
             (is', t'') <- instantiate (n - 1) t'
             return (TyArg u : is', t'')
        instantiate n (TThen p t) =
          do vr <- newRef Nothing
             require p vr
             (is, t') <- instantiate (n - 1) t
             return (PrArg (VGoal (Goal ("v", vr))) : is, t')

unify0 :: HasCallStack => Ty -> Ty -> UnifyM (Maybe Evid)
unify0 (TVar i _ _) (TVar j _ _)
  | i == j = return (Just VRefl)
unify0 (TUnif n (Goal (_, r)) t) (TUnif n' (Goal (_, r')) t')
  | n == n', r == r' = return (Just VRefl)
unify0 actual t@(TUnif n (Goal (uvar, r)) k) =
  do mt <- readRef r
     case mt of
       Just t -> unify' actual (shiftTN 0 n t)
       Nothing ->
         do chk <- canUpdate r
            if chk
            then do actual' <- flattenT actual
                    expectK actual' (kindOf actual') k
                    trace ("About to shiftTN 0 " ++ show (negate n) ++ " (" ++ show actual' ++ ")")
                    writeRef r (Just (shiftTN 0 (negate n) actual'))
                    trace ("1 instantiating " ++ uvar ++ " to " ++ show (shiftTN 0 (negate n) actual'))
                    return (Just VRefl)
            else return Nothing
unify0 (TUnif n (Goal (uvar, r)) k) expected =
  do mt <- readRef r
     case mt of
       Just t -> unify' (shiftTN 0 n t) expected
       Nothing ->
         do chk <- canUpdate r
            if chk
            then do expected' <- flattenT expected
                    expectK expected' (kindOf expected') k
                    trace ("About to shiftTN 0 " ++ show (negate n) ++ " (" ++ show expected' ++ ")")
                    writeRef r (Just (shiftTN 0 (negate n) expected'))
                    trace ("1 instantiating " ++ uvar ++ " to " ++ show (shiftTN 0 (negate n) expected'))
                    return (Just VRefl)
            else return Nothing
unify0 t u@(TInst {}) =
  unifyInstantiating t u unify'
unify0 t@(TInst {}) u =
  unifyInstantiating u t (flip unify')
unify0 TFun TFun = return (Just VRefl)
unify0 (TThen pa ta) (TThen px tx) =
  liftM2 VEqThen <$> unifyP pa px <*> unify' ta tx

unify0 t@(TApp {}) (u@(TApp {}))
  | TUnif {} <- ft = unifySpines
  | TUnif {} <- fu = unifySpines
  | otherwise      =
      do mq <- checking $ unify' ft fu
         case mq of
           Nothing -> refine $ requireEq t u
           Just q  ->
             do mqs <- zipWithM unify' ts us
                case sequence mqs of
                  Nothing -> return Nothing
                  Just qs -> return (Just (foldl VEqApp q qs))
  where (ft, ts) = spine t
        (fu, us) = spine u

        unifySpines =
          do mq <- unify' ft fu
             mqs <- zipWithM unify' ts us
             case sequence (mq : mqs) of
               Nothing -> return Nothing
               Just (q : qs) -> return (Just (foldl VEqApp q qs))
unify0 (TApp (TMapFun fa) ra) (TRow xs@(tx:_)) =
  do gs <- replicateM (length xs) (typeGoal' "t" (kindOf tx))
     unify' ra (TRow gs)
     sequence_ [unify' (TApp fa ta) tx | (ta, tx) <- zip gs xs]
     return (Just VEqMap)  -- wrong
unify0 a@(TForall xa (Just ka) ta) x@(TForall xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then liftM VEqForall <$> bindTy ka (unify' ta tx)
     else do trace $ "1 incoming unification failure: " ++ show a ++ ", " ++ show x
             return Nothing
unify0 a@(TLam xa (Just ka) ta) x@(TLam xx (Just kx) tx) =  -- Note: this case is missing from higher.pdf, also doubtful
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then liftM VEqLambda <$> bindTy ka (unify' ta tx)
     else do trace $ "2 incoming unification failure: " ++ show a ++ ", " ++ show x
             return Nothing
unify0 (TLab sa) (TLab sx)
  | sa == sx = return (Just VRefl)
unify0 (TSing ta) (TSing tx) =
  liftM VEqSing <$> unify' ta tx
unify0 (TLabeled la ta) (TLabeled lx tx) =
  liftM2 VEqLabeled <$> unify' la lx <*> unify' ta tx
unify0 (TRow ra) (TRow rx) =
  liftM VEqRow . sequence <$> zipWithM unify' ra rx
unify0 (TPi ra) (TPi rx) =
  liftM (VEqCon Pi) <$> unify' ra rx
unify0 (TPi r) u
  | TRow [t] <- r = liftM (VTrans (VEqTyConSing Pi)) <$> unify' t u
  | TLabeled tl tt <- u = liftM (`VTrans` VEqTyConSing Pi) <$> unify' r (TRow [u])
unify0 t (TPi r)
  | TRow [u] <- r = liftM (`VTrans` VEqTyConSing Pi) <$> unify' t u
  | TLabeled tl tt <- t = liftM (`VTrans` VEqTyConSing Pi) <$> unify' (TRow [t]) r
unify0 (TSigma ra) (TSigma rx) =
  liftM (VEqCon Sigma) <$> unify' ra rx
unify0 (TSigma r) u
  | TRow [t] <- r = liftM (VTrans (VEqTyConSing Sigma)) <$> unify' t u
  | TLabeled tl tt <- u = liftM (`VTrans` VEqTyConSing Sigma) <$> unify' r (TRow [u])
unify0 t (TSigma r)
  | TRow [u] <- r = liftM (`VTrans` VEqTyConSing Sigma) <$> unify' t u
  | TLabeled tl tt <- t = liftM (`VTrans` VEqTyConSing Sigma) <$> unify' (TRow [t]) r
unify0 a@(TMapFun f) x@(TMapFun g) =  -- note: wrong
  do q <- unify' f g
     case q of
       Just VRefl -> return (Just VRefl)
       Just q     -> return (Just (VEqMapCong q))
       Nothing    ->
        do trace $ "3 incoming unification failure: " ++ show a ++ ", " ++ show x
           return Nothing
unify0 t u
  | TApp {} <- t = refine $ requireEq t u
  | TApp {} <- u = refine $ requireEq t u
  | otherwise =
      do trace $ "5 incoming unification failure: " ++ show t ++ " ~/~ " ++ show u
         return Nothing


class HasTyVars t where
  subst :: MonadRef m => Int -> Ty -> t -> m t

instance HasTyVars Ty where
  subst j t (TVar i w k)
    | i == j = return t
    | otherwise = return (TVar i w k)
  subst v t u@(TUnif n (Goal (y, r)) k) =
    do mt <- readRef r
       case mt of
         Nothing -> return u
         Just u  -> do u' <- subst v t (shiftTN 0 n u)
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
  subst v t (TPi u) = TPi <$> subst v t u
  subst v t (TSigma u) = TSigma <$> subst v t u
  subst v t (TInst (Known is) u) = TInst <$> (Known <$> mapM substI is) <*> subst v t u where
    substI (TyArg u) = TyArg <$> subst v t u
    substI (PrArg v) = return (PrArg v)
  subst v t (TInst i@(Unknown (Goal (_, r))) u) =
    do minst <- readRef r
       case minst of
         Nothing -> TInst i <$> subst v t u
         Just is -> subst v t (TInst (Known is) u)
  subst v t (TMapFun f) = TMapFun <$> subst v t f
  subst v t (TMapArg f) = TMapArg <$> subst v t f
  subst v t u = error $ "internal: subst " ++ show v ++ " (" ++ show t ++ ") (" ++ show u ++")"

instance HasTyVars Pred where
  subst v t (PLeq y z) = PLeq <$> subst v t y <*> subst v t z
  subst v t (PPlus x y z) = PPlus <$> subst v t x <*> subst v t y <*> subst v t z

normalize' :: (HasCallStack, MonadCheck m) => Ty -> m (Ty, Evid)
normalize' t =
  do (u, q) <- normalize t
     theKCtxt <- asks kctxt
     case q of
       VRefl -> return (u, q)
       _     -> do trace $ "normalize (" ++ show t ++ ") -->* (" ++ show u ++ ") in " ++ show theKCtxt
                   return (u, q)

normalize :: (HasCallStack, MonadCheck m) => Ty -> m (Ty, Evid)
normalize t@(TVar i _ _) =
  do (_, mdef) <- asks ((!! i) . kctxt)
     case mdef of
       Nothing -> return (t, VRefl)
       Just def -> do (t', q) <- normalize (shiftTN 0 (i + 1) def)
                      return (t', VTrans VEqDefn q)
normalize t0@(TApp (TLam x (Just k) t) u) =
  do t1 <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 u) t
     (t2, q) <- normalize t1
     return (t2, VTrans VEqBeta q)
normalize (TApp (TPi r) t) =
  do (t1, q) <- normalize (TPi (TApp (TMapArg r) t))  -- To do: check kinding
     return (t1, VTrans (VEqLiftTyCon Pi) q)
normalize (TApp (TSigma r) t) =
  do (t1, q) <- normalize (TSigma (TApp (TMapArg r) t))
     return (t1, VTrans (VEqLiftTyCon Sigma) q)
normalize (TApp (TMapFun f) (TRow es))
  | Just ls <- mapM label es, Just ts <- mapM labeled es =
    do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (TApp f) ts)))
       return (t, VTrans VEqMap q)
-- The next rule implements `map id == id`
normalize (TApp (TMapFun f) z)
  | TLam _ k (TVar 0 _ _) <- f =
    do (z, q) <- normalize z
       return (z, VTrans VEqMapId q)
-- The following rules (attempt to) implement `map f . map g == map (f . g)`.
-- The need for special cases arises from our various ways to represent type
-- functions: they're not all `TLam`. There are probably some cases missing: in
-- particular, I see nothing about nested maps.
normalize (TApp (TMapFun (TLam _ _ f)) (TApp (TMapFun (TLam v k g)) z)) =
  do f' <- subst 0 g f
     (t, q) <- normalize (TApp (TMapFun (TLam v k f')) z)
     return (t, VTrans VEqMapCompose q)
normalize (TApp (TMapFun (TLam v (Just (KFun KType KType)) f)) (TApp (TMapFun TFun) z)) =
  do f' <- subst 0 (TApp TFun (TVar 0 v (Just KType))) f
     (t, q) <- normalize (TApp (TMapFun (TLam v (Just KType) f')) z)
     return (t, VTrans VEqMapCompose q)
normalize (TApp (TMapFun TFun) (TApp (TMapFun (TLam v k f)) z)) =
  do (t, q) <- normalize (TApp (TMapFun (TLam v k (TApp TFun f))) z)
     return (t, VTrans VEqMapCompose q)
normalize (TApp (TMapArg (TRow es)) t)
  | Just ls <- mapM label es, Just fs <- mapM labeled es =
    do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (`TApp` t) fs)))
       return (t, VTrans VEqMapCompose q)
normalize (TMapArg z)
  | KRow (KFun k1 k2) <- kindOf z =
    return (TLam "X" (Just k1) (TApp (TMapFun (TLam "Y" (Just (KFun k1 k2)) (TApp (TVar 0 "Y" (Just (KFun k1 k2))) (TVar 1 "X" (Just k1))))) (shiftTN 0 1 z)), VEqDefn)
normalize (TApp t1 t2) =
  do (t1', q1) <- normalize t1
     q1' <- flattenV q1
     case q1' of
       VRefl -> do (t2', q2) <- normalize t2
                   return (TApp t1 t2', VEqApp VRefl q2)
       _ -> do (t', q) <- normalize (TApp t1' t2)
               return (t', VTrans (VEqApp q1 VRefl) q)
normalize (TLabeled tl te) =
  do (tl', ql) <- normalize tl
     (te', qe) <- normalize te
     return (TLabeled tl' te', VEqLabeled ql qe)
normalize (TRow ts) =
  do (ts', qs) <- unzip <$> mapM normalize ts
     return (TRow ts', VEqRow qs)
normalize (TSigma z) =
  do (z', q) <- normalize z
     return (TSigma z', VEqCon Sigma q)
normalize (TPi z) =
  do (z', q) <- normalize z
     return (TPi z', VEqCon Pi q)
normalize (TForall x (Just k) t) =
  do (t', q) <- bindTy k (normalize t)
     return (TForall x (Just k) t', q) -- probably should be a congruence rule mentioned around here.... :)
normalize (TMapFun t) =
  do (t', q) <- normalize t
     return (TMapFun t', q)
normalize (TInst ig@(Unknown (Goal (_, r))) t) =
  do minsts <- readRef r
     case minsts of
       Nothing -> first (TInst ig) <$> normalize t
       Just is -> normalize (TInst (Known is) t)
normalize (TInst (Known is) t) =
  do is' <- mapM normI is
     first (TInst (Known (map fst is'))) <$> normalize t  -- TODO: should probably do something with the evidence here, but what. Not sure this case should even really be possible...
  where normI (TyArg t) = first TyArg <$> normalize t
        normI (PrArg v) = return (PrArg v, VRefl)
-- TODO: remaining homomorphic cases
normalize t = return (t, VRefl)

normalizeP :: MonadCheck m => Pred -> m Pred -- no evidence structure for predicate equality yet soooo....
normalizeP (PLeq x y) = PLeq <$> (fst <$> normalize x) <*> (fst <$> normalize y)
normalizeP (PPlus x y z) = PPlus <$> (fst <$> normalize x) <*> (fst <$> normalize y) <*> (fst <$> normalize z)
normalizeP (PEq t u) = PEq <$> (fst <$> normalize t) <*> (fst <$> normalize u)

unifyP :: Pred -> Pred -> UnifyM (Maybe Evid)
unifyP (PLeq y z) (PLeq y' z') = liftM2 VEqLeq <$> unify' y y' <*> unify' z z'
unifyP (PPlus x y z) (PPlus x' y' z') = liftM3 VEqPlus <$> unify' x x' <*> unify' y y' <*> unify' z z'

typeGoal :: MonadCheck m => String -> m Ty
typeGoal s =
  do s' <- fresh ("t$" ++ s)
     (flip (TUnif 0) KType) . Goal . (s',) <$> newRef Nothing

typeGoal' :: MonadCheck m => String -> Kind -> m Ty
typeGoal' s k =
  do s' <- fresh ("t$" ++ s)
     (flip (TUnif 0) k) . Goal . (s',) <$> newRef Nothing
