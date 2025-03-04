module Checker.Preds where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Data.IORef
import Data.List
import Data.Maybe (isNothing)

import Checker.Monad
import Checker.Unify
import Syntax

import GHC.Stack
import Data.Bifunctor

solve :: HasCallStack => (TCIn, Pred, IORef (Maybe Evid)) -> CheckM Bool
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

  cond :: Monad m => m Bool -> m a -> m a -> m a
  cond b c a = do b' <- b
                  if b' then c else a

  suppose :: Monad m => m Bool -> m (Maybe a) -> m (Maybe a)
  suppose b c = cond b c (return Nothing)

  everything p =
    do pctxt' <- mapM flattenP (pctxt cin)
       trace ("Solving " ++ show p ++ " from " ++ show pctxt')
       prim p <|> mapFunApp p <|> byAssump (pctxt cin) p

  sameSet :: Eq a => [a] -> [a] -> Bool
  sameSet xs ys = all (`elem` ys) xs && all (`elem` xs) ys

  allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
  allM p xs = and <$> mapM p xs

  typesEqual :: Ty -> Ty -> CheckM Bool
  typesEqual t u =
    do q <- check t u
       return (not (isNothing q))

  sameAssocs :: Eq a => [(a, Ty)] -> [(a, Ty)] -> CheckM Bool
  sameAssocs xs ys =
    allM (\(xl, xt) ->
      case lookup xl ys of
        Nothing -> return False
        Just yt ->
          do xt' <- fst <$> normalize xt
             yt' <- fst <$> normalize yt
             trace $ "4 sameAssocs (" ++ show xt' ++ ") (" ++ show yt' ++ ")"
             typesEqual xt' yt') xs

  unifyAssocs :: Eq a => [(a, Ty)] -> [(a, Ty)] -> CheckM ()
  unifyAssocs xs ys =
    mapM_ (\(xl, xt) ->
      case lookup xl ys of
        Nothing -> error $ "internal: unifyAssocs called with unmatched assoc lists"
        Just yt ->
          do q <- unify xt yt
             case q of
               Nothing -> fundeps p q
               Just _  -> return ()) xs

  matchLeqDirect, matchLeqMap, matchPlusDirect, match :: HasCallStack => Pred -> (Int, Pred) -> CheckM (Maybe Evid)
  match p q = matchLeqDirect p q <|> matchLeqMap p q <|> matchPlusDirect p q

  matchLeqDirect (PLeq y z) (v, PLeq y' z') =
    suppose (typesEqual y y') $
    suppose (typesEqual z z') $
    return (Just (VVar v))
  matchLeqDirect _ _ = return Nothing

  matchLeqMap (PLeq (TRow es) (TApp (TMapFun f) z)) (v, PLeq (TRow es') z') =
    suppose (typesEqual z z') $
    case (mapM splitLabel es, mapM splitLabel es') of
      (Just ps, Just ps') | sameSet (map fst ps) (map fst ps') ->
        do trace "1 match"
           unifyAssocs ps (map (second (TApp f)) ps')
           return (Just (VVar v))
           -- cond (sameAssocs ps (map (second (TApp f)) ps'))
           --      (do trace "2 match"
           --          return (Just (VVar v)))
           --      (do trace "3 no match"
           --          return Nothing)
      _ -> return Nothing
  matchLeqMap _ _ = return Nothing

  matchPlusDirect p@(PPlus x y z) (v, q@(PPlus x' y' z')) =
    suppose (typesEqual x x') $
      (suppose (typesEqual y y') (forceFD z z') <|>
       suppose (typesEqual z z') (forceFD y y')) <|>
    suppose (typesEqual y y') (suppose (typesEqual z z') (forceFD x x'))
    where forceFD t t' =
            do q <- unify t t'
               return (Just (VVar v))
               -- case flattenQ <$> q of
               --   Just QRefl -> return (Just (VVar v))
               --   _          ->
               --    do trace $ "matchPlusDirect: unifying (" ++ show t ++ ") and (" ++ show t' ++ ") gave (" ++ show q ++ ")"
               --       fundeps p q
  matchPlusDirect _ _ = return Nothing

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
       return ()
       -- case flattenQ <$> q of
       --   Just QRefl -> return ()
       --   _ -> throwError (ErrTypeMismatchPred p t u)

  -- May want to consider moving away from pattern matching for failure and
  -- towards using the `Maybe`ness...

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

  -- FIXME: these rules are just wrong

  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TApp (TMapFun f') z)) =
    do force p f f'
       fmap (VLeqLiftL f) <$> everything (PLeq y z)
  mapFunApp p@(PLeq (TRow []) (TApp (TMapFun f) z)) =
    fmap (VLeqLiftL f) <$> everything (PLeq (TRow []) z)
  mapFunApp p@(PLeq (TRow y) (TApp (TMapFun f) z))
    | TLam v (Just k) (TVar i w _) <- f  -- I think this case should actually have been normalized away....
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel y =
      fmap (VPredEq (VEqLeq (VEqMap `VTrans` VEqRow [ VEqSym VEqBeta | t <- ts]) VRefl) .
            VLeqLiftL f) <$> everything (PLeq (TRow y) z)
  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TRow [])) =
    fmap (VLeqLiftL f) <$> everything (PLeq y (TRow []))
  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TRow z))
    | Just (ls, fs, es) <- funCallsFrom z =
      do mapM_ (force p f) fs
         fmap (VLeqLiftL f) <$> everything (PLeq y (TRow (zipWith TLabeled ls es)))
    | TLam v (Just k) (TVar i w _) <- f
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel z =
      fmap (VPredEq (VEqLeq VRefl (VEqMap `VTrans` VEqRow [ VEqSym VEqBeta | t <- ts])) .
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
  censor (const (TCOut [])) $
  do (x, TCOut goals) <- listen m
     loop goals
     return x
