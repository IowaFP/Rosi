module Checker.Unify where

import Control.Monad
import Control.Monad.IO.Class

import Checker.Monad
import Checker.Types
import Syntax

unify :: Ty -> Ty -> CheckM (Maybe TyEqu)
unify (TVar i _ _) (TVar j _ _)
  | i == j = return (Just QRefl)
unify (TUnif (Goal (_, r)) k) expected =
  do mt <- readRef r
     case mt of
       Just t -> unify t expected
       Nothing ->
         do expected' <- flattenT expected
            expectK expected' (kindOf expected') k
            writeRef r (Just expected')
            return (Just QRefl)
unify actual (TUnif (Goal (_, r)) k) =
  do mt <- readRef r
     case mt of
       Just t -> unify actual t
       Nothing ->
         do actual' <- flattenT actual
            expectK actual' (kindOf actual') k
            writeRef r (Just actual')
            return (Just QRefl)
unify TFun TFun = return (Just QRefl)
unify (TThen pa ta) (TThen px tx) =
  liftM2 QThen <$> unifyP pa px <*> unify ta tx
unify a@(TForall xa ka ta) x@(TForall xx kx tx) =  -- To do: equate variables? For now, assuming they're identical
  do ksUnify <- unifyK ka kx
     if xa == xx && ksUnify == Just 0
     then liftM QForall <$> unify ta tx
     else do trace $ "1 incoming unification failure: " ++ show a ++ ", " ++ show x
             return Nothing
unify a@(TLam xa ka ta) x@(TLam xx kx tx) =  -- To do: as above.  Note: this case is missing from higher.pdf
  do ksUnify <- unifyK ka kx
     if xa == xx && ksUnify == Just 0
     then liftM QLambda <$> unify ta tx
     else do trace $ "2 incoming unification failure: " ++ show a ++ ", " ++ show x
             return Nothing
unify actual@(TApp {}) expected = unifyNormalizing actual expected
unify actual expected@(TApp {}) = unifyNormalizing actual expected
unify (TLab sa) (TLab sx)
  | sa == sx = return (Just QRefl)
unify (TSing ta) (TSing tx) =
  liftM QSing <$> unify ta tx
unify (TLabeled la ta) (TLabeled lx tx) =
  liftM2 QLabeled <$> unify la lx <*> unify ta tx
unify (TRow ra) (TRow rx) =
  liftM QRow <$> (sequence <$> zipWithM unify ra rx)
unify (TPi ra) (TPi rx) =
  liftM (QCon Pi) <$> unify ra rx
unify (TPi r) u
  | TRow [t] <- r = liftM (QTrans (QTyConSing Pi (TRow [t]) u)) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify (TPi r') u
         Nothing ->
           do expectK r k (KRow (kindOf u))
              writeRef tr (Just (TRow [u]))
              return (Just (QTyConSing Pi (TRow [u]) u))
unify t (TPi r)
  | TRow [u] <- r = liftM (`QTrans` QTyConSing Pi t (TRow [u])) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify t (TPi r')
         Nothing ->
           do expectK r k (KRow (kindOf t))
              writeRef tr (Just (TRow [t]))
              return (Just (QTyConSing Pi (TRow [t]) t))
unify (TSigma ra) (TSigma rx) =
  liftM (QCon Sigma) <$> unify ra rx
unify (TSigma r) u
  | TRow [t] <- r = liftM (QTrans (QTyConSing Sigma (TRow [t]) u)) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify (TSigma r') u
         Nothing ->
           do expectK r k (KRow (kindOf u))
              writeRef tr (Just (TRow [u]))
              return (Just (QTyConSing Sigma (TRow [u]) u))
unify t (TSigma r)
  | TRow [u] <- r = liftM (`QTrans` QTyConSing Sigma t (TRow [u])) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify t (TSigma r')
         Nothing ->
           do expectK r k (KRow (kindOf t))
              writeRef tr (Just (TRow [t]))
              return (Just (QTyConSing Sigma (TRow [t]) t))
unify a@(TMapFun f) x@(TMapFun g) =
  do q <- unify f g
     case q of
       Just QRefl -> return (Just QRefl)
       Just _     -> return (Just QMapFun)
       Nothing    ->
        do trace $ "3 incoming unification failure: " ++ show a ++ ", " ++ show x
           return Nothing
unify a@(TMapArg f) x@(TMapArg g) =
  do q <- unify f g
     case q of
       Just QRefl -> return (Just QRefl)
       Just _     -> return (Just QMapFun)
       Nothing    ->
        do trace $ "4 incoming unification failure: " ++ show a ++ ", " ++ show x
           return Nothing
unify t u =
  do do trace $ "5 incoming unification failure: " ++ show t ++ ", " ++ show u
     return Nothing

-- Assumption: at least one of actual or expected is a `TApp`
unifyNormalizing actual expected =
  do (actual', qa) <- normalize actual
     (expected', qe) <- normalize expected
     case (flattenQ qa, flattenQ qe) of
       (QRefl, QRefl) ->
         case (actual', expected') of
           (TApp fa aa, TApp fx ax) ->
             liftM2 QApp <$> unify fa fx <*> unify aa ax
           (TApp (TMapFun fa) (TRow ts), tx) ->
             do unify (TRow [TApp fa ta | ta <- ts]) tx
                return (Just QMapFun)
           (TApp (TMapFun fa) ra, TRow []) ->
             do unify ra (TRow [])
                return (Just QMapFun)
           (TApp (TMapFun fa) ra, TRow xs@(tx:_)) ->
             do gs <- replicateM (length xs) (typeGoal' "t" (kindOf tx))
                unify ra (TRow gs)
                sequence_ [unify (TApp fa ta) tx | (ta, tx) <- zip gs xs]
                return (Just QMapFun)
           _ -> do trace $ "6 incoming unification failure: " ++ show actual' ++ ", " ++ show expected'
                   return Nothing
       (qa, qe) ->
         liftM (QTrans qa . (`QTrans` QSym qe)) <$>
         unify actual' expected'

-- Sigh

subst :: Int -> Ty -> Ty -> CheckM Ty
subst j t (TVar i w k)
  | i == j = return t
  | otherwise = return (TVar i w k)
subst v t u@(TUnif (Goal (y, r)) k) =
  do mt <- readRef r
     case mt of
       Nothing -> return u
       Just u  -> do u' <- subst v t u
                     writeRef r (Just u')
                     return u'
subst v t TFun = return TFun
subst v t (TThen p u) = TThen <$> substp v t p <*> subst v t u
subst v t (TForall w k u) = TForall w k <$> subst (v + 1) t u
subst v t (TLam w k u) = TLam w k <$> subst (v + 1) t u
subst v t (TApp u0 u1) =
  TApp <$> subst v t u0 <*> subst v t u1
subst v t u@(TLab _) = return u
subst v t (TSing u) = TSing <$> subst v t u
subst v t (TLabeled l u) = TLabeled <$> subst v t l <*> subst v t u
subst v t (TRow us) = TRow <$> mapM (subst v t) us
subst v t (TPi u) = TPi <$> subst v t u
subst v t (TSigma u) = TSigma <$> subst v t u
subst v t (TMapFun f) = TMapFun <$> subst v t f
subst v t (TMapArg f) = TMapArg <$> subst v t f
subst v t u = error $ "internal: subst " ++ show v ++ " (" ++ show t ++ ") (" ++ show u ++")"

substp :: Int -> Ty -> Pred -> CheckM Pred
substp v t (PLeq y z) = PLeq <$> subst v t y <*> subst v t z
substp v t (PPlus x y z) = PPlus <$> subst v t x <*> subst v t y <*> subst v t z

normalize :: Ty -> CheckM (Ty, TyEqu)
normalize (TApp (TLam x k t) u) =
  do t1 <- subst 0 u t
     (t2, q) <- normalize t1
     return (t2, QTrans (QBeta x k t u t1) q)
normalize (TApp (TPi r) t) =
  do (t1, q) <- normalize (TPi (TApp (TMapArg r) t))  -- To do: check kinding
     return (t1, QTrans (QLiftTyCon Pi r t) q)
normalize (TApp (TSigma r) t) =
  do (t1, q) <- normalize (TSigma (TApp (TMapArg r) t))
     return (t1, QTrans (QLiftTyCon Sigma r t) q)
normalize (TApp (TMapFun f) (TRow es))
  | Just ls <- mapM label es, Just ts <- mapM labeled es =
    do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (TApp f) ts)))
       return (t, QTrans QMapFun q)
normalize (TApp (TMapFun f) z)
  | TLam v k (TVar i w _) <- f
  , v == w =
    do (z, q) <- normalize z
       return (z, QTrans QMapFun q)
  | TLam v k t <- f
  , KRow (KFun _ _) <- kindOf z =
    do (t, q) <- normalize =<< subst 0 (TMapArg z) t
       return (t, QTrans QMapFun q)
normalize (TApp (TMapArg (TRow es)) t)
  | Just ls <- mapM label es, Just fs <- mapM labeled es =
    do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (`TApp` t) fs)))
       return (t, QTrans QMapArg q)
normalize (TApp t1 t2) =
  do (t1', q1) <- normalize t1
     case flattenQ q1 of
       QRefl -> do (t2', q2) <- normalize t2
                   return (TApp t1 t2', QApp QRefl q2)
       _ -> do (t', q) <- normalize (TApp t1' t2)
               return (t', QTrans (QApp q1 QRefl) q)
normalize (TLabeled tl te) =
  do (tl', ql) <- normalize tl
     (te', qe) <- normalize te
     return (TLabeled tl' te', QLabeled ql qe)
normalize (TRow ts) =
  do (ts', qs) <- unzip <$> mapM normalize ts
     return (TRow ts', QRow qs)
normalize (TSigma z) =
  do (z', q) <- normalize z
     return (TSigma z', QCon Sigma q)

normalize t = return (t, QRefl)

unifyP :: Pred -> Pred -> CheckM (Maybe PrEqu)
unifyP (PLeq y z) (PLeq y' z') = liftM2 QLeq <$> unify y y' <*> unify z z'
unifyP (PPlus x y z) (PPlus x' y' z') = liftM3 QPlus <$> unify x x' <*> unify y y' <*> unify z z'

typeGoal :: String -> CheckM Ty
typeGoal s =
  (`TUnif` KType) . Goal . ("t$" ++ s,) <$> newRef Nothing

typeGoal' :: String -> Kind -> CheckM Ty
typeGoal' s k =
  (`TUnif` k) . Goal . ("t$" ++ s,) <$> newRef Nothing
