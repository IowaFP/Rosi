{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=50 #-}
module Checker.Unify (module Checker.Unify) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (first)
import Data.List (elemIndex, partition, sortOn)
import Data.Maybe (fromJust, isNothing)

import Checker.Monad
import Checker.Normalize
import Checker.Promote
import Checker.Types hiding (trace)
import Checker.Utils
import Printer
import Syntax

import GHC.Stack
import qualified Debug.Trace as T

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

unify, check :: HasCallStack => [Eqn] -> Ty -> Ty -> CheckM (Maybe Evid)
unify eqns actual expected =
  do (result, (undoes, preds)) <- runReaderT (runWriterT $ evalStateT (runUnifyM $ unify' actual expected) Nothing) eqns
     if isNothing result
     then mapM_ perform undoes
     else tell (TCOut preds)
     return result

check eqns actual expected =
  do (result, (undoes, preds)) <- runReaderT (runWriterT $ evalStateT (runUnifyM $ unify' actual expected) (Just [])) eqns
     if isNothing result
     then mapM_ perform undoes
     else tell (TCOut  preds)
     return result

data ProductiveUnification = Productive Evid | Unproductive | UnificationFails

unifyProductive eqns actual expected =
  do (result, (undoes, preds)) <- runReaderT (runWriterT $ evalStateT (runUnifyM $ unify' actual expected) Nothing) eqns
     result' <- traverse flattenV result
     case result' of
       Nothing ->
         do mapM_ perform undoes
            return UnificationFails
       Just (VGoal _) ->
         do mapM_ perform undoes
            return Unproductive
       Just v ->
         do tell (TCOut preds)
            return (Productive v)

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
  do trace ("1 (" ++ renderString False (ppr actual) ++ ") ~ (" ++ renderString False (ppr expected) ++ ")")
     eqns <- theEqns
     (actual', q) <- normalize eqns actual
     (expected', q') <- normalize eqns expected
     -- TODO: do we need to renormalize each time around?
     let f = case q of
               VEqRefl -> id
               _       -> VEqTrans q
         f' = case q' of
               VEqRefl -> id
               _       -> VEqTrans (VEqSym q')
     ((f' . f) <$>) <$> unify0 actual' expected'

-- This function handles unification cases `t ~ u` where `u` starts with some
-- instantiation variables. If `t` start with instantiation variables instead,
-- pass it as `u` but pass `flip unify` as the third argument.
--
-- TODO: somewhere should check that provided instantiations have the expected
-- kinds
unifyInstantiating :: Ty -> Ty -> (Ty -> Ty -> UnifyM (Maybe Evid)) -> UnifyM (Maybe Evid)
unifyInstantiating t u unify =
  do t' <- flattenT t
     u' <- flattenT u
     let(tqs, _) = quants t'
        (uis, u'') = insts u'
        nuqs      = length (fst (quants u''))
     -- trace $ unwords ["unifyInstantiating:", show t', ",", show u']
     case (t', u') of
       (TInst (Unknown _ g) t'', TInst (Unknown _ g') u'')
         | goalRef g == goalRef g' -> unify t'' u''
       (TForall {}, TInst (Unknown {}) (TUnif {})) ->
         return Nothing
       _
         | Just matches <- match (reverse (map reverseIs uis)) (reverse (take (length tqs - nuqs) tqs)) ->
             do trace $ unlines ["unifyInstantiating:", "    " ++ show (quants t'), "    " ++ show (insts u'), "    " ++ show matches]
                t'' <- instantiates (reverse matches) t'
                unify t'' u''
         | otherwise ->
             do trace $ "7 incoming unification failure: " ++ show t ++ " ~/~ " ++ show u
                return Nothing
  where -- match needs its arguments **reversed** from their appearance in the type
        match :: [Insts] -> [Quant] -> Maybe [Either (Either (Ty, Kind) (Evid, Pred)) (Int, Goal Insts, [Quant])]
        match [] [] = return []
        match [Unknown n g] qs = return [Right (n, g, reverse qs)]
        match (Unknown n g : is@(Known _ : _)) qs = (Right (n, g, reverse thens) :) <$> match is rest where
          isThen (QuThen _) = True
          isThen _          = False
          (thens, rest) = partition isThen qs
        match (Unknown n g : is@(Unknown _ _ : _)) qs
          | QuForall {} : _ <- qs = Nothing
          | otherwise = (Right (n, g, []) :) <$> match is qs
        match (Known is : is') qs =
          do (ms, qs') <- matchKnown is qs
             (ms ++) <$> match is' qs'
          where matchKnown [] qs = return ([], qs)
                matchKnown (TyArg t : is) (QuForall _ k : qs) = (first (Left (Left (t, k)) :)) <$> matchKnown is qs
                matchKnown (PrArg v : is) (QuThen p : qs) = first (Left (Right (v, p)) :) <$> matchKnown is qs
                matchKnown _ [] = T.trace "3 ruh-roh" Nothing
                matchKnown is qs = error $ "ruh-roh: " ++ show is ++ ", " ++ show qs
        match is qs =
          T.trace (unlines ["1 ruh-roh: in ", renderString False (ppr t), " ~ ", renderString False (ppr u), "misaligned " ++ show is ++ " and " ++ show qs])
          Nothing -- error $ unlines ["ruh-roh: in ", renderString False (ppr t), " ~ ", renderString False (ppr u), "misaligned " ++ show is ++ " and " ++ show qs]

        -- Need to write function to apply list of instantiations derived from
        -- `match` above. Problem is (a) need to work outside in, but (b)
        -- instantiation (as demonstrated below) needs to operate on the
        -- remainder of the type, which has been somewhat disassembled
        --
        -- Approach: go back to original type, using list of insts to guide
        -- instantiation??
        instantiates :: [Either (Either (Ty, Kind) (Evid, Pred)) (Int, Goal Insts, [Quant])] -> Ty -> UnifyM Ty
        instantiates [] t = return t
        instantiates (Left (Left (u, _)) : is) (TForall x k t) =
            do t' <- subst 0 (shiftTN 0 1 u) t
               instantiates is (shiftTN 0 (-1) t')
        instantiates (Left (Right _) : is) (TThen _ t) =
          instantiates is t
        instantiates (Right (n, Goal (ivar, r), qs) : is) t =
          do (is', t') <- instantiate (length qs) n t
             trace $ "instantiating " ++ ivar ++ " to " ++ show is'
             writeRef r (Just (Known is'))
             instantiates is t'
        instantiates is t =
          error $ "4 ruh-roh: (" ++ show is ++ ") (" ++ show t ++ ")"

        instantiate :: Int -> Int -> Ty -> UnifyM ([Inst], Ty)
        instantiate 0 _ t = return ([], t)
        instantiate n m (TForall x (Just k) t) =
          do u <- typeGoal' x k
             t' <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 u) (shiftTN 0 m t)
             (is', t'') <- instantiate (n - 1) m t'
             return (TyArg u : is', t'')
        instantiate n m (TThen p t) =
          do vr <- newRef Nothing
             require p vr
             (is, t') <- instantiate (n - 1) m t
             return (PrArg (VGoal (Goal ("v", vr))) : is, t')

        reverseIs :: Insts -> Insts
        reverseIs is@(Unknown {}) = is
        reverseIs (Known is) = Known (reverse is)

unify0 :: HasCallStack => Ty -> Ty -> UnifyM (Maybe Evid)
unify0 (TVar i _) (TVar j _)
  | i == j = return (Just VEqRefl)
unify0 (TUnif v) (TUnif w)
  | uvShift v == uvShift w, goalRef (uvGoal v) == goalRef (uvGoal w) = return (Just VEqRefl)
-- These next cases are totally not ad hoc nonsense
unify0 (TUnif v) (TInst (Unknown 0 (Goal (_, r))) (TUnif w))
  | v == w = do writeRef r (Just (Known []))
                return (Just VEqRefl)
unify0 (TInst (Unknown 0 (Goal (_, r))) (TUnif w)) (TUnif v)
  | v == w = do writeRef r (Just (Known []))
                return (Just VEqRefl)
unify0 actual t@(TUnif v@(UV n lref (Goal (uvar, r)) k)) =
  do mt <- readRef r
     case mt of
       Just t -> unify' actual (shiftTN 0 n t)
       Nothing ->
         do chk <- canUpdate r
            if chk
            then solveUV v actual
            else return Nothing
unify0 actual@(TUnif v@(UV n lref (Goal (uvar, r)) k)) expected =
  do mt <- readRef r
     case mt of
       Just t -> unify' (shiftTN 0 n t) expected
       Nothing ->
         do chk <- canUpdate r
            if chk
            then solveUV v expected
            else return Nothing
unify0 (TInst (Unknown n i1) t) (TInst (Unknown n' i2) u)
  | n == n' && i1 == i2 = unify' t u
unify0 t u@(TInst {}) =
  do mq <- unifyInstantiating t u unify'
     case mq of
       Nothing -> refine $ requireEq t u
       Just q  -> return (Just q)
unify0 t@(TInst {}) u =
  do mq <- unifyInstantiating u t (flip unify')
     case mq of
       Nothing -> refine $ requireEq t u
       Just q  -> return (Just q)
unify0 TFun TFun = return (Just VEqRefl)
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

        unifySpines  = unifySpines' ft' ts' fu' us'
          where m = length ts
                n = length us
                (ts0, ts') = splitAt (m - n) ts
                ft' = foldl TApp ft ts0
                (us0, us') = splitAt (n - m) us
                fu' = foldl TApp fu us0

        unifySpines' ft ts fu us =
          do mq <- unify' ft fu
             mqs <- zipWithM unify' ts us
             case sequence (mq : mqs) of
               Nothing -> return Nothing
               Just (q : qs) -> return (Just (foldl VEqApp q qs))

unify0 (TApp (TMapFun fa) ra) (TRow xs@(tx:_)) =
  do KFun kdom kcod <- kindOf fa
     gs <- replicateM (length xs) (typeGoal' "t" kdom)
     ls <- replicateM (length xs) (typeGoal' "l" KLabel)
     mq <- unify' ra (TRow (zipWith TLabeled ls gs))
     mqs <- sequence [unify' (TLabeled tl (TApp fa ta)) tx | (tl, ta, tx) <- zip3 ls gs xs]
     case (mq, sequence mqs) of
       (Just q, Just qs) -> return (Just VEqMap)  -- wrong
       _            -> return Nothing
unify0 (TRow xs@(tx:_)) (TApp (TMapFun fa) ra) =
  do KFun kdom kcod <- kindOf fa
     gs <- replicateM (length xs) (typeGoal' "t" kdom)
     ls <- replicateM (length xs) (typeGoal' "l" KLabel)
     mq <- unify' ra (TRow (zipWith TLabeled ls gs))
     mqs <- sequence [unify' (TLabeled tl (TApp fa ta)) tx | (tl, ta, tx) <- zip3 ls gs xs]
     case (mq, sequence mqs) of
       (Just q, Just qs) -> return (Just VEqMap)  -- wrong
       _                 -> return Nothing

unify0 a@(TForall xa (Just ka) ta) x@(TForall xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then liftM VEqForall <$> bindTy ka (unify' ta tx)
     else do trace $ "1 incoming unification failure: " ++ show a ++ " ~/~ " ++ show x
             return Nothing
unify0 a@(TLam xa (Just ka) ta) x@(TLam xx (Just kx) tx) =  -- Note: this case is missing from higher.pdf, also doubtful
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then liftM VEqLambda <$> bindTy ka (unify' ta tx)
     else do trace $ "2 incoming unification failure: " ++ show a ++ " ~/~ " ++ show x
             return Nothing
unify0 (TLab sa) (TLab sx)
  | sa == sx = return (Just VEqRefl)
unify0 (TSing ta) (TSing tx) =
  liftM VEqSing <$> unify' ta tx
unify0 (TLabeled la ta) (TLabeled lx tx) =
  liftM2 VEqLabeled <$> unify' la lx <*> unify' ta tx
unify0 (TRow [t]) (TRow [u]) =
  do q <- unify' t u
     return (VEqRow . (:[]) <$> q)
unify0 (TRow ra) (TRow rx)
  | length ra == length rx =
      do qs <- sequence <$> zipWithM unify' ra rx
         return (VEqRow <$> qs)
--   | Just as <- mapM splitLabel ra, Just xs <- mapM splitLabel rx, Just is <- sameSet (map fst as) (map fst xs) =
--       do qs <- sequence [unify' a (fromJust x) | (l, a) <- as, let x = lookup l xs]
--          return (VEqTrans (VEqRowPermute is) . VEqRow <$> sequence qs)
--   where sameSet xs ys
--           | Just is <- sequence [elemIndex y xs | y <- ys], all (`elem` ys) xs =
--               Just is
--           | otherwise = Nothing
unify0 (TPi ra) (TPi rx) =
  liftM (VEqCon Pi) <$> unify' ra rx
unify0 (TPi r) u
  | TRow [t] <- r = liftM (VEqTrans (VEqTyConSing Pi)) <$> unify' t u
  | TLabeled tl tt <- u = liftM (`VEqTrans` VEqTyConSing Pi) <$> unify' r (TRow [u])
unify0 t (TPi r)
  | TRow [u] <- r = liftM (`VEqTrans` VEqSym (VEqTyConSing Pi)) <$> unify' t u
  | TLabeled tl tt <- t = liftM (`VEqTrans` VEqSym (VEqTyConSing Pi)) <$> unify' (TRow [t]) r
unify0 (TSigma ra) (TSigma rx) =
  liftM (VEqCon Sigma) <$> unify' ra rx
unify0 (TSigma r) u
  | TRow [t] <- r = liftM (VEqTrans (VEqTyConSing Sigma)) <$> unify' t u
  | TLabeled tl tt <- u = liftM (`VEqTrans` VEqTyConSing Sigma) <$> unify' r (TRow [u])
unify0 t (TSigma r)
  | TRow [u] <- r = liftM (`VEqTrans` VEqSym (VEqTyConSing Sigma)) <$> unify' t u
  | TLabeled tl tt <- t = liftM (`VEqTrans` VEqSym (VEqTyConSing Sigma)) <$> unify' (TRow [t]) r
unify0 (TMu f) (TMu g) =
  liftM (VEqCon Mu) <$> unify' f g
unify0 TString TString =
  return (Just VEqRefl)
unify0 a@(TMapFun f) x@(TMapFun g) =  -- note: wrong
  do q <- unify' f g
     case q of
       Just VEqRefl -> return (Just VEqRefl)
       Just q       -> return (Just (VEqMapCong q))
       Nothing      ->
        do trace $ "3 incoming unification failure: " ++ show a ++ " ~/~ " ++ show x
           return Nothing
unify0 t@(TCompl x y) u@(TCompl x' y') =
  checking $ do mqx <- unify' x x'
                mqy <- unify' y y'
                case (mqx, mqy) of
                  (Just qx, Just qy) -> return (Just (VEqComplCong qx qy))
                  _                  -> refine $ requireEq t u
unify0 t@(TCompl {}) u = refine $ requireEq t u
unify0 t u@(TCompl {}) = refine $ requireEq t u
unify0 t u
  | (not (null ts) && refinable ft) ||
    (not (null us) && refinable fu) = refine $ requireEq t u
  | otherwise =
      do trace $ "5 incoming unification failure: " ++ show t ++ " ~/~ " ++ show u
         return Nothing
  where (ft, ts) = spine t
        (fu, us) = spine u
        refinable (TUnif {}) = True
        refinable _          = False

unifyP :: Pred -> Pred -> UnifyM (Maybe Evid)
unifyP (PLeq y z) (PLeq y' z') = liftM2 VEqLeq <$> unify' y y' <*> unify' z z'
unifyP (PPlus x y z) (PPlus x' y' z') = liftM3 VEqPlus <$> unify' x x' <*> unify' y y' <*> unify' z z'

typeGoal :: MonadCheck m => String -> m Ty
typeGoal s =
  do s' <- fresh s
     l  <- theLevel
     TUnif . (flip (UV 0 l) KType) . Goal . (s',) <$> newRef Nothing

typeGoal' :: MonadCheck m => String -> Kind -> m Ty
typeGoal' s k =
  do s' <- fresh s
     l  <- theLevel
     TUnif . (flip (UV 0 l) k) . Goal . (s',) <$> newRef Nothing
