{-# LANGUAGE CPP #-}
module Checker.Unify (module Checker.Unify) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor       (first)
import Data.Foldable
import Data.Sequence        (Seq ((:<|), (:|>)))

import Checker.Monad
import Checker.Normalize
import Checker.Promote
import Checker.Types        hiding (trace)
import Checker.Utils
import Printer
import Syntax

import GHC.Stack

#define __unificationFails(t, u) do { trace (show __LINE__ ++ " incoming unification failure " ++ renderString (ppr (t)) ++ " ~/~ " ++ renderString (ppr (u))); unificationFails (t) (u)}

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

unify, check :: HasCallStack => [Eqn] -> Ty -> Ty -> CheckM (Either (Ty, Ty) Evid)
unify eqns actual expected =
  do trace ("1 (" ++ renderString (ppr actual) ++ ") ~ (" ++ renderString (ppr expected) ++ ")")
     m <- mark
     (result, preds) <- runReaderT (runWriterT $ evalStateT (runExceptT $ runUnifyM $ unify' actual expected) Nothing) eqns
     case result of
       Right q ->
         do tell (TCOut preds [])
            return (Right q)
       Left err ->
         do reset m
            return (Left err)

check eqns actual expected =
  do trace ("2 (" ++ renderString (ppr actual) ++ ") ~ (" ++ renderString (ppr expected) ++ ")")
     m <- mark
     (result, preds) <- runReaderT (runWriterT $ evalStateT (runExceptT $ runUnifyM $ unify' actual expected) (Just [])) eqns
     case result of
       Right q ->
         do tell (TCOut preds [])
            return (Right q)
       Left err ->
         do reset m
            return (Left err)

data ProductiveUnification = Productive Evid | Unproductive | UnificationFails (Ty, Ty)

unifyProductive eqns actual expected =
  do trace ("3 (" ++ renderString (ppr actual) ++ ") ~ (" ++ renderString (ppr expected) ++ ")")
     m <- mark
     (result, preds) <- runReaderT (runWriterT $ evalStateT (runExceptT $ runUnifyM $ unify' actual expected) Nothing) eqns
     case result of
       Right q ->
         do q' <- flatten q
            case q' of
              VGoal _ ->
                do reset m
                   return Unproductive
              _ ->
                do tell (TCOut preds [])
                   return (Productive q')
       Left err ->
         do reset m
            return  (UnificationFails err)

checking :: UnifyM t -> UnifyM t
checking m =
  do s <- get
     bracket
       (put (Just []))
       m
       (put s)

requireEq :: Ty -> Ty -> UnifyM Evid
requireEq t u =
  do s <- get
     case s of
       -- Shortcut: if we're in checking mode, then we only want to succeed when
       -- the types exactly align. If we've gotten this far, then we already
       -- know the equation isn't solved by updating one of the local uvars, so
       -- no need to check...
       Just _ -> __unificationFails(t, u)
       Nothing ->
         do v <- newRef Nothing
            require (PEq t u) v
            return (VGoal (Goal ("q", v)))

unify' :: HasCallStack => Ty -> Ty -> UnifyM Evid
unify' actual expected =
  do eqns <- theEqns
     (actual', q) <- normalize eqns actual
     (expected', q') <- normalize eqns expected
     trace ("4 (" ++ renderString (ppr actual') ++ ") ~ (" ++ renderString (ppr expected') ++ ")")
     let f = case q of
               VEqRefl -> id
               _       -> VEqTrans q
         f' = case q' of
               VEqRefl -> id
               _       -> VEqTrans (VEqSym q')
     f' . f <$> unify0 actual' expected'

-- This function handles unification cases `t ~ u` where `u` starts with some
-- instantiation variables. If `t` start with instantiation variables instead,
-- pass it as `u` but pass `flip unify` as the third argument.
unifyInstantiating :: Ty -> Ty -> (Ty -> Ty -> UnifyM Evid) -> UnifyM Evid
unifyInstantiating t u unify =
  do t' <- flatten t
     u' <- flatten u

     let (uis, u'') = insts u'
     case (t', u') of
       (TInst [Unknown _ g] t'', TInst [Unknown _ g'] u'')
         | goalRef g == goalRef g' -> unify t'' u''
       _ -> universals t' uis u'' -- loop t' uis u''

  where
    ---------------------------------------------------------------------------
    -- Universals
    ---------------------------------------------------------------------------

    universals :: Ty -> Seq Inst -> Ty -> UnifyM Evid -- InstantiationStep
    universals (TForall _ Nothing _) _ _ =
      error "Unannoted forall in instantiation!"
    -- Match a forall against an explicit type argument and instantiate
    universals (TForall _ (Just k) t) (TyArg s :<| is) u =
      do s' <- liftToUnifyM . toCheckM $ checkTy s k
         t' <- beta t s'
         universals t' is u
    -- An explicit type argument without an initial forall is a unification
    -- failure.
    universals t is@(TyArg _ :<| _) u =
      __unificationFails(t, (TInst (toList is) u))
    universals t@(TForall {}) is@(Unknown {} :<| Unknown {} :<| _) u =
      existentials t is u
    -- Defer instantiations of metavariables
    universals t@(TUnif {}) is u =
      existentials t is u
    -- If there's an instantiation before a type argument, and there are
    -- predicates to be solved, solve them. This is weird corner case, but could
    -- arise with a type like `forall x. P x => forall y. ...`
    universals t (Unknown n g :<| is@(TyArg _ :<| _)) u =
      do writeRef (goalRef g) . Just =<< mapM solve ps
         universals t' is u
      where (ps, t') = thens t
            thens :: Ty -> ([Pred], Ty)
            thens (TThen p t) = first (p :) (thens t)
            thens t           = ([], t)
            solve p =
              do vr <- newRef Nothing
                 require p vr
                 return (PrArg (VGoal (Goal ("v", vr))))
    -- Defer instantiations where RHS is a metavarible---might later be
    -- instantiated with quantifiers or more instantiations.
    universals t@(TForall {}) is@(Unknown {} :<| _) u@(TUnif {}) =
      existentials t is u
    universals t is u
      | null qts, TExists {} <- u =
        existentials t is u
      -- Fewer (but some!) forall-like quantifiers on the left than on the
      -- right. In this case, we fall back on trying to unify the left and
      -- right-hand side directly, after solving any remaining unification
      -- variables to the empty sequence.
      | length qts <= length qus =
        do mapM_ solveEmpty is
           unify t u
      -- More forall-like quantifiers on the left. We solve the additional
      -- prefix of the left-hand side. We know that `is'` is either (a) empty or
      -- (b) a `TyPack`, because otherwise we would have hit one of the previous
      -- cases. Because the unknown instantiation might also need to capture
      -- existentials, we generate a fresh unknown instantiation to add to the
      -- end of our solution.
      | Unknown n g :<| is' <- is =
        do (insts, ts) <- solve n (take (length qts - length qus) qts) []
           t'' <- instantiate shiftNV n ts (quantify (drop (length qts - length qus) qts) t')
           gr <- newRef Nothing
           name <- fresh "i"
           let i' = Unknown n (Goal (name, gr))
           writeRef (goalRef g) (Just (insts ++ [i']))
           universals t'' (i' :<| is') u
      -- Don't actually know how this case is possible, but if we do get here
      -- we're out of ideas.
      | otherwise =
        do trace $ "4 incoming unification failure " ++ renderString (ppr t) ++ " ~ " ++ renderString (ppr (TInst (toList is) u))
           __unificationFails(t, TInst (toList is) u)

      where (qts, t') = univQuants t
            (qus, _) = univQuants u

            solveEmpty (Unknown n g) =
              writeRef (goalRef g) (Just [])
            solveEmpty _ =
              __unificationFails(t, TInst (toList is) u)

            solve :: Int -> [Quant] -> [Ty] -> UnifyM ([Inst], [Ty])
            solve _ [] us =
              return ([], us)
            solve n (QuForall x k : qs) us =
              do u <- typeGoal' x k
                 first (TyArg u :) <$> solve n qs (u : us)
            solve n (QuThen p : qs) us =
              do vr <- newRef Nothing
                 p' <- instantiate shiftNV n us p
                 require p' vr
                 first (PrArg (VGoal (Goal ("v", vr))) :) <$> solve n qs us
            solve _ _ _ = error "impossible, working on foralls"

            instantiate shift n us t =
              shift [] 0 (- m) <$> foldM (\t (i, u) -> subst i u t) t us'
              where us' = zip [0..] (map (shiftN 0 (m + n)) us)
                    m   = length us

    ---------------------------------------------------------------------------
    -- Existentials
    ---------------------------------------------------------------------------

    existentials :: Ty -> Seq Inst -> Ty -> UnifyM Evid -- InstantiationStep
    existentials _ _ (TExists _ Nothing _) =
      error "Unannotated exists in instantiation!"
    -- Match an existential against an explicit type argument and instantiate
    existentials t (is :|> TyPack s) (TExists _ (Just k) u) =
      do s' <- liftToUnifyM . toCheckM $ checkTy s k
         u' <- beta u s'
         existentials t is u'
    -- An explicit pack without an initial exists is a unification failure.
    existentials t is@(_ :|> TyPack _) u =
      __unificationFails(t, TInst (toList is) u)
    -- Defer ambiguous packs
    existentials t is@(_ :|> Unknown {} :|> Unknown {}) u@(TExists {}) =
      -- unificationFails t (TInst (toList is) u)
      requireEq t (TInst (toList is) u)
    -- Defer packing of metavariables
    existentials t is u@(TUnif {}) =
      -- unificationFails t (TInst (toList is) u)
      requireEq t (TInst (toList is) u)
    -- If there's an instantiation before a pack, and there are existential
    -- predicates intervening, then pack them. This is also a weird corner case,
    -- and would arise with a type like `exists x. P x => exists y. ...`
    existentials t (is@(_ :|> TyPack _) :|> Unknown n g) u =
      do writeRef (goalRef g) . Just =<< mapM solve ps
         existentials t is u'
      where (ps, u') = thens u
            thens :: Ty -> ([Pred], Ty)
            thens (TExistsP p t) = first (p :) (thens t)
            thens t              = ([], t)
            solve p =
              do vr <- newRef Nothing
                 require p vr
                 return (PrPack (VGoal (Goal ("v", vr))))
    existentials t@(TUnif {}) is@(_ :|> Unknown {}) u@(TExists {}) =
      -- unificationFails t (TInst (toList is) u)
      requireEq t (TInst (toList is) u)
    existentials t is u
      | null qus, TForall {} <- t =
        -- unificationFails t (TInst (toList is) u)
        requireEq t (TInst (toList is) u)
      -- Fewer (but some!) exists-like quantifiers on the right than on the
      -- left. In this case, we fall back on trying to unify the left and
      -- right-hand side directly, after solving any remaining unification
      -- variables to the empty sequence.
      | length qus <= length qts =
        do mapM_ solveEmpty is
           unify t u
      -- More exists-like quantifiers on the right. We solve the additional
      -- prefix of the right-hand side. We know that `is'` is either (a) empty or
      -- (b) a `TyArg`, because otherwise we would have hit one of the previous
      -- cases. Because the unknown instantiation might also need to capture
      -- universals, we generate a fresh unknown instantiation to add to the
      -- end of our solution.
      | is' :|> Unknown n g <- is =
        do (insts, us) <- solve n (take (length qus - length qts) qus) []
           u'' <- instantiate shiftNV n us (quantify (drop (length qus - length qts) qus) u')
           gr <- newRef Nothing
           name <- fresh "i"
           let i' = Unknown n (Goal (name, gr))
           writeRef (goalRef g) (Just (insts ++ [i']))
           existentials t (is' :|> i') u''
      -- Don't actually know how this case is possible, but if we do get here
      -- we're out of ideas.
      | otherwise =
        __unificationFails(t, TInst (toList is) u)

      where (qts, _) = existQuants t
            (qus, u') = existQuants u

            solveEmpty (Unknown n g) =
              writeRef (goalRef g) (Just [])
            solveEmpty _ =
              __unificationFails(t, TInst (toList is) u)

            solve :: Int -> [Quant] -> [Ty] -> UnifyM ([Inst], [Ty])
            solve _ [] us =
              return ([], us)
            solve n (QuExists x k : qs) us =
              do u <- typeGoal' x k
                 first (TyPack u :) <$> solve n qs (u : us)
            solve n (QuExistsP p : qs) us =
              do vr <- newRef Nothing
                 p' <- instantiate shiftNV n us p
                 require p' vr
                 first (PrPack (VGoal (Goal ("v", vr))) :) <$> solve n qs us
            solve _ _ _ = error "impossible, working on foralls"

            instantiate shift n us t =
              shift [] 0 (- m) <$> foldM (\t (i, u) -> subst i u t) t us'
              where us' = zip [0..] (map (shiftN 0 (m + n)) us)
                    m   = length us

unify0 :: HasCallStack => Ty -> Ty -> UnifyM Evid

-------------------------------------------------------------------------------
-- Identity cases: type variables and unification variables
-------------------------------------------------------------------------------

unify0 (TVar i _) (TVar j _)
  | i == j = return VEqRefl
unify0 (TUnif v) (TUnif w)
  | goalRef (uvGoal v) == goalRef (uvGoal w) = return VEqRefl
-- Solve instantiations around identical types
unify0 (TUnif v) (TInst [Unknown 0 (Goal (_, r))] (TUnif w))
  | v == w = do writeRef r (Just [])
                return VEqRefl
unify0 (TInst [Unknown 0 (Goal (_, r))] (TUnif w)) (TUnif v)
  | v == w = do writeRef r (Just [])
                return VEqRefl
-- This case doesn't seem to trigger. I don't know that it's *wrong*, tho.
-- unify0 (TInst [Unknown n i1] t) (TInst [Unknown n' i2] u)
--   | n == n' && i1 == i2 = unify' t u

--------------------------------------------------------------------------------
-- Unification variables
--------------------------------------------------------------------------------

unify0 actual t@(TUnif v@(UV n lref (Goal (uvar, r)) k)) =
  do mt <- readRef r
     case mt of
       Just t -> unify' actual (shiftN 0 n t)
       Nothing ->
         do chk <- canUpdate r
            if chk
            then do mq <- solveUV v actual
                    case mq of
                      Nothing -> __unificationFails(actual, t)
                      Just q  -> return q
            else __unificationFails(t, actual)
unify0 actual@(TUnif v@(UV n lref (Goal (uvar, r)) k)) expected =
  do mt <- readRef r
     case mt of
       Just t -> unify' (shiftN 0 n t) expected
       Nothing ->
         do chk <- canUpdate r
            if chk
            then do mq <- solveUV v expected
                    case mq of
                      Nothing -> __unificationFails(actual, expected)
                      Just q  -> return q
            else __unificationFails(actual, expected)

--------------------------------------------------------------------------------
-- Instantiations
--------------------------------------------------------------------------------

unify0 t u@(TInst {}) =
  unifyInstantiating t u unify'
unify0 t@(TInst {}) u =
  unifyInstantiating u t (flip unify')

--------------------------------------------------------------------------------
-- Type constructors, of various forms and varieties
--------------------------------------------------------------------------------

unify0 TFun TFun = return VEqRefl
unify0 (TThen pa ta) (TThen px tx) =
  VEqThen <$> unifyP pa px <*> unify' ta tx
unify0 (TExistsP pa ta) (TExistsP px tx) =
  VEqExistsP <$> unifyP pa px <*> unify' ta tx
unify0 a@(TForall xa (Just ka) ta) x@(TForall xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then VEqForall <$> bindTy ka (unify' ta tx)
     else __unificationFails(a, x)
unify0 a@(TExists xa (Just ka) ta) x@(TExists xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then VEqExists <$> bindTy ka (unify' ta tx)
     else __unificationFails(a, x)
unify0 a@(TLam xa (Just ka) ta) x@(TLam xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then VEqLambda <$> bindTy ka (unify' ta tx)
     else __unificationFails(a, x)
unify0 (TLab sa) (TLab sx)
  | sa == sx = return VEqRefl
unify0 (TSing ta) (TSing tx) =
  VEqSing <$> unify' ta tx
unify0 (TLabeled la ta) (TLabeled lx tx) =
  VEqLabeled <$> unify' la lx <*> unify' ta tx
unify0 (TRow [t]) (TRow [u]) =
  do q <- unify' t u
     return (VEqRow [q])
unify0 t@(TRow ra) u@(TRow rx)
  | length ra == length rx =
      do qs <- zipWithM unify' ra rx
         return (VEqRow qs)
  | otherwise = __unificationFails(t, u)
unify0 (TConApp Pi ra) (TConApp Pi rx) =
  VEqCon Pi <$> unify' ra rx
unify0 (TConApp Sigma ra) (TConApp Sigma rx) =
  VEqCon Sigma <$> unify' ra rx
-- When unifying mus, we choose the count that results in fewer remaining
-- expansions. I think the idea here was to prevent some kind of
-- unification/normalization loop that would keep resetting the count, but I
-- hardly know if that is even possible...
unify0 (TConApp (Mu count) f) (TConApp (Mu count') g) =
  VEqCon (Mu count'') <$> unify' f g where
    count'' = case (count, count') of
                (Unexpanded, Unexpanded) -> Unexpanded
                (Unexpanded, Expanded n) -> Expanded n
                (Expanded m, Unexpanded) -> Expanded m
                (Expanded m, Expanded n) -> Expanded (min m n)
unify0 t0@(TConApp (TCUnif g) t) u =
  do mk <- readRef (goalRef g)
     case mk of
       Just k -> unify0 (TConApp k t) u
       Nothing -> case u of
                    TConApp k u' ->
                       do writeRef (goalRef g) (Just k)
                          VEqCon k <$> unify0 t u'
                    _ -> __unificationFails(t0, u)
unify0 t u0@(TConApp (TCUnif g) u) =
  do mk <- readRef (goalRef g)
     case mk of
       Just k -> unify0 t (TConApp k u)
       Nothing -> case t of
                    TConApp k t' ->
                       do writeRef (goalRef g) (Just k)
                          VEqCon k <$> unify0 t' u
                    _ -> __unificationFails(t, u0)
unify0 TString TString =
  return VEqRefl
unify0 a@(TMap f) x@(TMap g) =
  do mq <- try $ checking $ unify' f g
     case mq of
       Just VEqRefl -> return VEqRefl
       Just q       -> return (VEqMapCong q)
       Nothing      -> do q' <- requireEq f g
                          return (VEqMapCong q')
-- Just because x - y ~ z - w, we don't acutally know anything about x, y, z and
-- w. We try a couple of options here---if we know that x ~ z or y ~ w, then we
-- can fix the otherwise, but if those don't work then we can't make progress.
unify0 t@(TCompl x y) u@(TCompl x' y') =
  do mq <- try $ checking $ unify' x x'
     case mq of
       Just qx -> do qy <- unify' y y'
                     return $ VEqComplCong qx qy
       Nothing ->
         do mq <- try $ checking $ unify' y y'
            case mq of
              Just qy -> do qx <- unify' x x'
                            return $ VEqComplCong qx qy
              Nothing -> requireEq t u
unify0 t@(TCompl {}) u = requireEq t u
unify0 t u@(TCompl {}) = requireEq t u

---------------------------------------------------------------------------------
-- Applications
---------------------------------------------------------------------------------

unify0 (TApp (TMap fa) ra) (TRow []) =
  do q <- unify' ra (TRow [])
     return VEqMap
unify0 (TApp (TMap fa) ra) (TRow xs@(tx:_)) =
  do KFun kdom kcod <- kindOf fa
     gs <- replicateM (length xs) (typeGoal' "t" kdom)
     ls <- replicateM (length xs) (typeGoal' "l" KLabel)
     q <- unify' ra (TRow (zipWith TLabeled ls gs))
     qs <- sequence [unify' (TLabeled tl (TApp fa ta)) tx | (tl, ta, tx) <- zip3 ls gs xs]
     return VEqMap  -- wrong
unify0 (TRow []) (TApp (TMap fa) ra) =
  do unify' (TRow []) ra
     return VEqMap
unify0 (TRow xs@(tx:_)) (TApp (TMap fa) ra) =
  do KFun kdom kcod <- kindOf fa
     gs <- replicateM (length xs) (typeGoal' "t" kdom)
     ls <- replicateM (length xs) (typeGoal' "l" KLabel)
     q <- unify' ra (TRow (zipWith TLabeled ls gs))
     qs <- sequence [unify' (TLabeled tl (TApp fa ta)) tx | (tl, ta, tx) <- zip3 ls gs xs]
     return VEqMap  -- wrong
unify0 t@(TApp {}) (u@(TApp {})) =
  do mq <- try $ checking $ unify' ft fu
     case mq of
       Nothing -> requireEq t u
       Just q  ->
         do qs <- zipWithM unify' ts us
            return (foldl VEqApp q qs)
  where (ft, ts) = spine t
        (fu, us) = spine u
unify0 t u
  | (TConApp (Mu count) f, ts) <- spine t, noHeadUnif u, Just count' <- decr count =
    unify' (foldl TApp f (TConApp (Mu count') f : ts)) u
  | (TConApp (Mu count) g, us) <- spine u, noHeadUnif t, Just count' <- decr count =
    unify' t (foldl TApp g (TConApp (Mu count') g : us))
  where noHeadUnif t
          | (TUnif _, _) <- spine t = False
          | otherwise               = True
        decr (Expanded 0) = Nothing
        decr (Expanded n) = Just (Expanded (n - 1))
        decr Unexpanded   = Just (Expanded 20)
unify0 t@(TApp {}) u
  | isUVarApp t = requireEq t u
  | otherwise   = __unificationFails(t, u)
  where (ft, _) = spine t
unify0 t u@(TApp {})
  | isUVarApp u = requireEq t u
  | otherwise   = __unificationFails(t, u)
  where (fu, _) = spine u

--------------------------------------------------------------------------------
-- We're out of tricks, so give up
--------------------------------------------------------------------------------

unify0 t u = __unificationFails(t, u)


---------------------------------------------------------------------------------
-- Unification: Predicates
---------------------------------------------------------------------------------

unifyP :: Pred -> Pred -> UnifyM Evid
unifyP (PLeq y z) (PLeq y' z')        = VEqLeq <$> unify' y y' <*> unify' z z'
unifyP (PPlus x y z) (PPlus x' y' z') = VEqPlus <$> unify' x x' <*> unify' y y' <*> unify' z z'
unifyP (PEq t u) (PEq t' u')          = VEqEq <$> unify' t t' <*> unify' u u'
unifyP (PFold z) (PFold z')           = VEqFold <$> unify' z z'
unifyP p q                            = __unificationFails(p `TThen` TConApp Pi (TRow []), q `TThen` TConApp Pi (TRow []))


