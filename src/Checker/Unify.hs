{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Checker.Unify (module Checker.Unify) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor       (first)
import Data.Foldable
import Data.Sequence        (Seq (Empty, (:<|), (:|>)))
import Data.Sequence        qualified as S

import Checker.Monad
import Checker.Normalize
import Checker.Promote
import Checker.Types        hiding (trace)
import Checker.Utils
import Printer
import Syntax

import GHC.Stack

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
         do q' <- flattenV q
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
       Just _ -> unificationFails t u
       Nothing ->
         do v <- newRef Nothing
            require (PEq t u) v
            return (VGoal (Goal ("q", v)))

data InstantiationStep = Progress Ty (Seq Inst) Ty | Defer | Inapplicable | Done Ty Ty
  deriving Show

instance Semigroup (UnifyM InstantiationStep) where
  m <> n =
    do result <- m
       case result of
         Inapplicable -> n
         _            -> return result

unify' :: HasCallStack => Ty -> Ty -> UnifyM Evid
unify' actual expected =
  do trace ("4 (" ++ renderString (ppr actual) ++ ") ~ (" ++ renderString (ppr expected) ++ ")")
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
     (f' . f) <$> unify0 actual' expected'

-- This function handles unification cases `t ~ u` where `u` starts with some
-- instantiation variables. If `t` start with instantiation variables instead,
-- pass it as `u` but pass `flip unify` as the third argument.
unifyInstantiating :: Ty -> Ty -> (Ty -> Ty -> UnifyM Evid) -> UnifyM Evid
unifyInstantiating t u unify =
  do t' <- flattenT t
     u' <- flattenT u
     let (tqs, _)   = univQuants t'
         (uis, u'') = insts u'
         nuqs       = length (fst (univQuants u''))
     case (t', u') of
       (TInst [Unknown _ g] t'', TInst [Unknown _ g'] u'')
         | goalRef g == goalRef g' -> unify t'' u''
       (TForall {}, TInst [Unknown {}] (TUnif {})) ->
         unificationFails t u
       _
         | Just matches <- match (uis) (take (length tqs - nuqs) tqs) ->
             do trace $ unlines ["unifyInstantiating:", "    " ++ show (univQuants t'), "    " ++ show (insts u'), "    " ++ show matches]
                t'' <- instantiates matches t'
                unify t'' u''
         | otherwise ->
             do trace $ "7 incoming unification failure: " ++ show t ++ " ~/~ " ++ show u
                unificationFails t u
  where
    match :: Seq Inst -> [Quant] -> Maybe [Either Inst (Int, Goal Insts, [Quant])]

    match Empty [] =
      return []

    match (Unknown n g :<| Empty) qs =
      return [Right (n, g, qs)]

    match (Unknown n g :<| is@(TyArg _ :<| _)) qs =
      (Right (n, g, here) :) <$> match is there
      where
        untilForall qs@(QuForall {} : _) = ([], qs)
        untilForall (q : qs)             = first (q :) (untilForall qs)
        untilForall []                   = ([], [])

        (here, there) = untilForall qs

    match (Unknown n g :<| is@(Unknown {} :<| _)) qs
      | QuForall {} : _ <- qs = Nothing
      | otherwise             = (Right (n, g, []) :) <$> match is qs

    match (TyArg t :<| is) (QuForall _ k : qs) = (Left (TyArg t) :) <$> match is qs
    match (PrArg v :<| is) (QuThen _ : qs)     = (Left (PrArg v) :) <$> match is qs

    match _ _ = Nothing

    -- Need to write function to apply list of instantiations derived from
    -- `match` above. Problem is (a) need to work outside in, but (b)
    -- instantiation (as demonstrated below) needs to operate on the
    -- remainder of the type, which has been somewhat disassembled
    --
    -- Approach: go back to original type, using list of insts to guide
    -- instantiation??
    instantiates :: [Either Inst (Int, Goal Insts, [Quant])] -> Ty -> UnifyM Ty
    instantiates [] t = return t
    instantiates _ (TForall x Nothing t) =
      error "Unannotated forall in instantiation!"
    instantiates (Left (TyArg u) : is) (TForall x (Just k) t) =
        do u' <- liftToUnifyM . toCheckM $ checkTy u k
           t' <- subst 0 (shiftTN 0 1 u) t
           instantiates is (shiftTN 0 (-1) t')
    instantiates (Left (PrArg _) : is) (TThen _ t) =
      instantiates is t
    instantiates (Right (n, Goal (ivar, r), qs) : is) t =
      do (is', t') <- instantiate (length qs) n t
         trace $ "instantiating " ++ ivar ++ " to " ++ show is'
         writeRef r (Just is')
         instantiates is t'
      where
        instantiate :: Int -> Int -> Ty -> UnifyM ([Inst], Ty)
        instantiate 0 _ t = return ([], t)
        instantiate n m (TForall x (Just k) t) =
          do u <- typeGoal' x k
             t' <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 (1 + m) u) t
             (is', t'') <- instantiate (n - 1) m t'
             return (TyArg u : is', t'')
        instantiate n m (TThen p t) =
          do vr <- newRef Nothing
             require p vr
             (is, t') <- instantiate (n - 1) m t
             return (PrArg (VGoal (Goal ("v", vr))) : is, t')
        instantiate n m t =
          error $ "instantiate " ++ show n ++ " " ++ show m ++ " (" ++ show t ++ ")"
    instantiates is t =
      error $ "4 ruh-roh: (" ++ show is ++ ") (" ++ show t ++ ")"

    ---------------------------------------------------------------------------
    -- Universals
    ---------------------------------------------------------------------------

    universals :: Ty -> Seq Inst -> Ty -> UnifyM InstantiationStep
    universals (TForall _ Nothing _) _ _ =
      error "Unannoted forall in instantiation!"
    -- Match a forall against an explicit type argument and instantiate
    universals (TForall _ (Just k) t) (TyArg s :<| is) u =
      do u' <- liftToUnifyM . toCheckM $ checkTy s k
         t' <- subst 0 (shiftTN 0 1 u') t
         return (Progress t' is u)
    -- An explicit type argument without an initial forall is a unification
    -- failure.
    universals t is@(TyArg _ :<| _) u =
      unificationFails t (TInst (toList is) u)
    -- Defer ambiguous instantiations
    universals (TForall {}) (Unknown {} :<| Unknown {} :<| is) u =
      return Defer
    -- Defer instantiations of metavariables
    universals (TUnif {}) _ u =
      return Defer
    -- If there's an instantiation before a type argument, and there are
    -- predicates to be solved, solve them. This is weird corner case, but could
    -- arise with a type like `forall x. P x => forall y. ...`
    universals t (Unknown n g :<| is@(TyArg _ :<| _)) u =
      do writeRef (goalRef g) . Just =<< mapM instantiate ps
         return (Progress t' is u)
      where (ps, t') = thens t
            thens :: Ty -> ([Pred], Ty)
            thens (TThen p t) = first (p :) (thens t)
            thens t           = ([], t)
            instantiate p =
              do vr <- newRef Nothing
                 require p vr
                 return (PrArg (VGoal (Goal ("v", vr))))
    universals t is u
      -- Fewer forall-like quantifiers on the left than on the right. In this
      -- case, we fall back on trying to unify the left and right-hand side
      -- directly, after solving any remaining unification variables to the
      -- empty sequence.
      | length qts <= length qus =
        do mapM_ solveEmpty is
           return (Done t u)
      | Unknown n g :<| is' <- is =
        undefined

      where (qts, t') = univQuants t
            (qus, u') = univQuants u

            solveEmpty (Unknown n g) =
              writeRef (goalRef g) (Just [])
            solveEmpty _ =
              unificationFails t (TInst (toList is) u)




unify0 :: HasCallStack => Ty -> Ty -> UnifyM Evid
unify0 (TVar i _) (TVar j _)
  | i == j = return VEqRefl
unify0 (TUnif v) (TUnif w)
  | uvShift v == uvShift w, goalRef (uvGoal v) == goalRef (uvGoal w) = return VEqRefl
-- These next cases are totally not ad hoc nonsense
unify0 (TUnif v) (TInst [Unknown 0 (Goal (_, r))] (TUnif w))
  | v == w = do writeRef r (Just [])
                return VEqRefl
unify0 (TInst [Unknown 0 (Goal (_, r))] (TUnif w)) (TUnif v)
  | v == w = do writeRef r (Just [])
                return VEqRefl
unify0 actual t@(TUnif v@(UV n lref (Goal (uvar, r)) k)) =
  do mt <- readRef r
     case mt of
       Just t -> unify' actual (shiftTN 0 n t)
       Nothing ->
         do chk <- canUpdate r
            if chk
            then do mq <- solveUV v actual
                    case mq of
                      Nothing -> unificationFails actual t
                      Just q  -> return q
            else unificationFails t actual
unify0 actual@(TUnif v@(UV n lref (Goal (uvar, r)) k)) expected =
  do mt <- readRef r
     case mt of
       Just t -> unify' (shiftTN 0 n t) expected
       Nothing ->
         do chk <- canUpdate r
            if chk
            then do mq <- solveUV v expected
                    case mq of
                      Nothing -> unificationFails actual expected
                      Just q  -> return q
            else unificationFails actual expected
unify0 (TInst [Unknown n i1] t) (TInst [Unknown n' i2] u)
  | n == n' && i1 == i2 = unify' t u
unify0 t u@(TInst {}) =
  do mq <- try $ unifyInstantiating t u unify'
     case mq of
       Nothing -> requireEq t u
       Just q  -> return q
unify0 t@(TInst {}) u =
  do mq <- try $ unifyInstantiating u t (flip unify')
     case mq of
       Nothing -> requireEq t u
       Just q  -> return q
unify0 TFun TFun = return VEqRefl
unify0 (TThen pa ta) (TThen px tx) =
  VEqThen <$> unifyP pa px <*> unify' ta tx
unify0 t@(TApp {}) (u@(TApp {}))
  | TUnif {} <- ft = requireEq t u -- unifySpines
  | TUnif {} <- fu = requireEq t u -- unifySpines
  | otherwise      =
      do mq <- try $ checking $ unify' ft fu
         case mq of
           Nothing -> requireEq t u
           Just q  ->
             do qs <- zipWithM unify' ts us
                return (foldl VEqApp q qs)
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
          do q <- unify' ft fu
             qs <- zipWithM unify' ts us
             return (Just (foldl VEqApp q qs))

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
unify0 a@(TForall xa (Just ka) ta) x@(TForall xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then VEqForall <$> bindTy ka (unify' ta tx)
     else do trace $ "1 incoming unification failure: " ++ show a ++ " ~/~ " ++ show x
             unificationFails a x
unify0 a@(TExists xa (Just ka) ta) x@(TExists xx (Just kx) tx) =
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then VEqExists <$> bindTy ka (unify' ta tx)
     else do trace $ "1a incoming unification failure: " ++ show a ++ " ~/~ " ++ show x
             unificationFails a x
unify0 a@(TLam xa (Just ka) ta) x@(TLam xx (Just kx) tx) =  -- Note: this case is missing from higher.pdf, also doubtful
  do ksUnify <- unifyK ka kx
     if ksUnify == Just 0
     then VEqLambda <$> bindTy ka (unify' ta tx)
     else do trace $ "2 incoming unification failure: " ++ show a ++ " ~/~ " ++ show x
             unificationFails a x
unify0 (TLab sa) (TLab sx)
  | sa == sx = return VEqRefl
unify0 (TSing ta) (TSing tx) =
  VEqSing <$> unify' ta tx
unify0 (TLabeled la ta) (TLabeled lx tx) =
  VEqLabeled <$> unify' la lx <*> unify' ta tx
unify0 (TRow [t]) (TRow [u]) =
  do q <- unify' t u
     return (VEqRow [q])
unify0 (TRow ra) (TRow rx)
  | length ra == length rx =
      do qs <- zipWithM unify' ra rx
         return (VEqRow qs)
unify0 (TConApp Pi ra) (TConApp Pi rx) =
  VEqCon Pi <$> unify' ra rx
unify0 (TConApp Sigma ra) (TConApp Sigma rx) =
  VEqCon Sigma <$> unify' ra rx
unify0 (TConApp (Mu count) f) (TConApp (Mu count') g) =
  VEqCon (Mu count'') <$> unify' f g where
    count'' = case (count, count') of
                (Unexpanded, Unexpanded) -> Unexpanded
                (Unexpanded, Expanded n) -> Expanded n
                (Expanded m, Unexpanded) -> Expanded m
                (Expanded m, Expanded n) -> Expanded (min m n)
unify0 t u
  | (TConApp (Mu count) f, ts) <- spine t, noHeadUnif u, Just count' <- decr count =
    unify' (foldl TApp f (TConApp (Mu count') f : ts)) u
  | (TConApp (Mu count) g, us) <- spine u, noHeadUnif t, Just count' <- decr count =
    unify' t (foldl TApp g (TConApp (Mu count') g : us))
  where noHeadUnif t
          | (TUnif _, _) <- spine t = False
          | otherwise = True
        decr (Expanded 0) = Nothing
        decr (Expanded n) = Just (Expanded (n - 1))
        decr Unexpanded   = Just (Expanded 20)
unify0 t0@(TConApp (TCUnif g) t) u =
  do mk <- readRef (goalRef g)
     case mk of
       Just k -> unify0 (TConApp k t) u
       Nothing -> case u of
                    TConApp k u' ->
                       do writeRef (goalRef g) (Just k)
                          VEqCon k <$> unify0 t u'
                    _ -> do trace $ "7 incoming unification failure: " ++ show t0 ++ " ~/~ " ++ show u
                            unificationFails t0 u
unify0 t u0@(TConApp (TCUnif g) u) =
  do mk <- readRef (goalRef g)
     case mk of
       Just k -> unify0 t (TConApp k u)
       Nothing -> case t of
                    TConApp k t' ->
                       do writeRef (goalRef g) (Just k)
                          VEqCon k <$> unify0 t' u
                    _ -> do trace $ "7 incoming unification failure: " ++ show t ++ " ~/~ " ++ show u0
                            unificationFails t u0
unify0 TString TString =
  return VEqRefl

unify0 a@(TMap f) x@(TMap g) =
  do mq <- try $ checking $ unify' f g
     case mq of
       Just VEqRefl -> return (VEqRefl)  -- shouldn't this be handled by flattenV?
       Just q       -> return (VEqMapCong q)
       Nothing      -> do q' <- requireEq f g
                          return (VEqMapCong q')

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
  -- checking $ do qx <- unify' x x'
  --               qy <- unify' y y'
  --               return (VEqComplCong qx qy)
unify0 t@(TCompl {}) u = requireEq t u
unify0 t u@(TCompl {}) = requireEq t u
unify0 t u
  | (not (null ts) && refinable ft) ||
    (not (null us) && refinable fu) = requireEq t u
  | otherwise =
      do trace $ "5 incoming unification failure: " ++ renderString (ppr t) ++ " ~/~ " ++ renderString (ppr u)
         unificationFails t u
  where (ft, ts) = spine t
        (fu, us) = spine u
        refinable (TUnif {}) = True
        refinable _          = False

unifyP :: Pred -> Pred -> UnifyM Evid
unifyP (PLeq y z) (PLeq y' z')        = VEqLeq <$> unify' y y' <*> unify' z z'
unifyP (PPlus x y z) (PPlus x' y' z') = VEqPlus <$> unify' x x' <*> unify' y y' <*> unify' z z'


