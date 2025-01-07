module Checker.Preds where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Data.IORef
import Data.List

import Checker.Monad
import Checker.Unify
import Syntax

import GHC.Stack
import Data.Bifunctor

solve :: HasCallStack => (CIn, Pred, IORef (Maybe Evid)) -> CheckM Bool
solve (cin, p, r) =
  local (const cin) $
  do -- mv <- everything . pushShiftsP =<< flattenP p
     mv <- everything =<< normalizeP =<< flattenP p
     case mv of
       Just v -> writeRef r (Just v) >> return True
       Nothing -> return False

  where

  (<|>) :: CheckM (Maybe a) -> CheckM (Maybe a) -> CheckM (Maybe a)
  m <|> n = maybe n (return . Just) =<< m

  infixr 2 <|>

  everything p =
    do pctxt' <- mapM flattenP (pctxt cin)
       trace ("Solving " ++ show p ++ " from " ++ show pctxt')
       prim p <|> mapFunApp p <|> byAssump (pctxt cin) p

  sameSet :: Eq a => [a] -> [a] -> Bool
  sameSet xs ys = all (`elem` ys) xs && all (`elem` xs) ys

  allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
  allM p xs = and <$> mapM p xs

  sameAssocs :: Eq a => [(a, Ty)] -> [(a, Ty)] -> CheckM Bool
  sameAssocs xs ys =
    allM (\(xl, xt) ->
      case lookup xl ys of
        Nothing -> return False
        Just yt ->
          do xt' <- fst <$> normalize xt
             yt' <- fst <$> normalize yt
             trace $ "4 sameAssocs (" ++ show xt' ++ ") (" ++ show yt' ++ ")"
             return (xt' == yt')) xs

  -- May want to consider moving away from pattern matching for failure and
  -- towards using the `Maybe`ness...

  match :: HasCallStack => Pred -> (Int, Pred) -> CheckM (Maybe Evid)
  match (PLeq y z) (v, PLeq y' z')
    | y == y' && z == z' = return (Just (VVar v))
  match (PLeq (TRow es) (TApp (TMapFun f) z)) (v, PLeq (TRow es') z')
    | z == z'
    , Just ps <- mapM splitLabel es
    , Just ps' <- mapM splitLabel es'
    , sameSet (map fst ps) (map fst ps') =
      do trace "1 match"
         b <- sameAssocs ps (map (second (TApp f)) ps')
         if b
         then do trace "2 match"
                 return (Just (VVar v))
         else do trace "3 no match"
                 return Nothing
  match p@(PPlus x y z) (v, q@(PPlus x' y' z'))
    | xEqual && yEqual = forceFD z z'
    | xEqual && zEqual = forceFD y y'
    | yEqual && zEqual = forceFD x x'
    | otherwise = return Nothing

    where xEqual = x == x'
          yEqual = y == y'
          zEqual = z == z'

          forceFD t t' =
            do q <- unify t t'
               case flattenQ <$> q of
                 Just QRefl -> return (Just (VVar v))
                 _          -> fundeps p q

  match p q = return Nothing

  -- question to self: why do I have both the `fundeps` error and the `force` error?

  fundeps p q = throwError (ErrTypeMismatchFD p q)

  expand1 :: Pred -> [Pred]
  expand1 (PPlus x y z) = [PLeq x z, PLeq y z]
  expand1 (PLeq _ _) = []

  expand2 :: Pred -> Pred -> [Pred]
  expand2 (PLeq x y) (PLeq z w)
    | y == z = [PLeq x w]
    | x == w = [PLeq z y]
  expand2 _ _ = []

  expandAll :: [Pred] -> [Pred]
  expandAll = go [] where
    go qs [] = qs
    go qs (p : ps) = go (p : qs) (ps' ++ ps) where
      ps' = expand1 p ++ concatMap (expand2 p) qs

  byAssump as p =
    do as' <- mapM (normalizeP <=< flattenP) as
       trace ("Expanding " ++ show as')
       let as'' = expandAll as'
       trace ("Expanded " ++ show as' ++ " to " ++ show as'' ++ "; solving " ++ show p)
       go (zip [0..] as'') p where
    go [] p = return Nothing
    go (a : as) p = match p a <|> go as p

  force p t u =
    do q <- unify t u
       case flattenQ <$> q of
         Just QRefl -> return ()
         _ -> throwError (ErrTypeMismatchPred p t u)

  prim p@(PLeq (TRow y) (TRow z))
    | Just yd <- mapM label y, Just zd <- mapM label z =
      case sequence [elemIndex e zd | e <- yd] of
        Nothing -> return Nothing
        Just is ->
          do mapM_ (\(i, TLabeled _ t) -> let TLabeled _ u = z !! i in force p t u) (zip is y)
             return (Just (VLeqSimple is))
  prim (PPlus (TRow x) (TRow y) (TRow z))
    | Just xd <- mapM label x, Just yd <- mapM label y, Just zd <- mapM label z =
      case sequence [(Left <$> elemIndex e xd) `mplus` (Right <$> elemIndex e yd) | e <- zd] of
        Nothing -> return Nothing
        Just is ->
          do mapM_ align (zip is z)
             return (Just (VPlusSimple is))
    where align (Left i, TLabeled _ t) = force p t u where TLabeled _ u = x !! i
          align (Right i, TLabeled _ t) = force p t u where TLabeled _ u = y !! i
  prim _ = return Nothing

  funCallsFrom :: [Ty] -> Maybe ([Ty], [Ty], [Ty])
  funCallsFrom z
    | Just ls <- mapM label z
    , Just ts <- mapM labeled z
    , Just (fs, es) <- mapAndUnzipM tyAppFrom ts = return (ls, fs, es)
    | otherwise                                  = Nothing
    where tyAppFrom (TApp f e) = Just (f, e)
          tyAppFrom _          = Nothing

  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TApp (TMapFun f') z)) =
    do force p f f'
       fmap (VLeqLiftL f) <$> everything (PLeq y z)
  mapFunApp p@(PLeq (TRow []) (TApp (TMapFun f) z)) =
    fmap (VLeqLiftL f) <$> everything (PLeq (TRow []) z)
  mapFunApp p@(PLeq (TRow y) (TApp (TMapFun f) z))
    | TLam v k (TVar i w _) <- f  -- I think this case should actually have been normalized away....
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel y =
      fmap (VPredEq (QLeq (QMapFun `QTrans` QRow [ QSym (QBeta v k (TVar i v (Just k)) t t) | t <- ts]) QRefl) .
            VLeqLiftL f) <$> everything (PLeq (TRow y) z)
  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TRow [])) =
    fmap (VLeqLiftL f) <$> everything (PLeq y (TRow []))
  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TRow z))
    | Just (ls, fs, es) <- funCallsFrom z =
      do mapM_ (force p f) fs
         fmap (VLeqLiftL f) <$> everything (PLeq y (TRow (zipWith TLabeled ls es)))
    | TLam v k (TVar i w _) <- f
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel z =
      fmap (VPredEq (QLeq QRefl (QMapFun `QTrans` QRow [ QSym (QBeta v k (TVar i v (Just k)) t t) | t <- ts])) .
            VLeqLiftL f) <$> everything (PLeq y (TRow z))
  mapFunApp p@(PPlus (TApp (TMapFun f) x) (TApp (TMapFun g) y) (TApp (TMapFun h) z)) =
    do force p f g
       force p g h
       fmap (VPlusLiftL f) <$> everything (PPlus x y z)
  mapFunApp _ = return Nothing


loop :: [Problem] -> CheckM ()
loop [] = return ()
loop ps =
  do (b, ps') <- once False [] ps
     if b
     then loop ps'
     else throwError . ErrNotEntailed =<< mapM notEntailed ps'
  where once b qs [] = return (b, qs)
        once b qs (p : ps) =
          do b' <- solve p
             once (b || b')
                  (if b' then qs else p : qs)
                  ps
        notEntailed (cin, p, _) =
          do p' <- flattenP p
             ps' <- mapM flattenP (pctxt cin)
             return (p', ps')

andSolve :: CheckM a -> CheckM a
andSolve m =
  censor (const (COut [])) $
  do (x, COut goals) <- listen m
     loop goals
     return x
