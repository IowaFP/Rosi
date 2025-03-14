module Checker.Preds (module Checker.Preds) where

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
  do trace $ "solve: " ++ show p
     as' <- mapM (normalizeP [] <=< flattenP) (pctxt cin)
     trace ("Expanding " ++ show as')
     let as'' = expandAll (zip as' [VVar i | i <- [0..]])
     let eqns = pickEqns as''
     trace ("Expanded " ++ show as' ++ " to " ++ show as'' ++ "; solving " ++ show p)
     trace ("Found equations " ++ show eqns)
     p' <- normalizeP eqns =<< flattenP p
     trace ("Normalized goal to " ++ show p')
     mv <- everything as'' p'
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

  pickEqns :: [(Pred, Evid)] -> [Eqn]
  pickEqns ps = go ps where
    go [] = []
    go ((PEq (TCompl z x) y, v) : ps) = (TCompl z x, (y, v)) : go ps
    go (_ : ps) = go ps

  everything as p =
    do trace ("Solving " ++ show p)
       v <- prim p <|> refl p <|> mapFunApp as p <|> byAssump as p
       trace ("Solved " ++ show p ++ " by " ++ show v)
       return v

  sameSet :: Eq a => [a] -> [a] -> Bool
  sameSet xs ys = all (`elem` ys) xs && all (`elem` xs) ys

  allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
  allM p xs = and <$> mapM p xs

  typesEqual :: Ty -> Ty -> CheckM Bool
  typesEqual t u =
    do q <- check [] t u
       return (not (isNothing q))

  sameAssocs :: Eq a => [(a, Ty)] -> [(a, Ty)] -> CheckM Bool
  sameAssocs xs ys =
    allM (\(xl, xt) ->
      case lookup xl ys of
        Nothing -> return False
        Just yt ->
          do xt' <- fst <$> normalize [] xt
             yt' <- fst <$> normalize [] yt
             trace $ "4 sameAssocs (" ++ show xt' ++ ") (" ++ show yt' ++ ")"
             typesEqual xt' yt') xs

  forceAssocs :: Eq a => [(a, Ty)] -> [(a, Ty)] -> CheckM ()
  forceAssocs xs ys =
    mapM_ (\(xl, xt) ->
      case lookup xl ys of
        Nothing -> error $ "internal: unifyAssocs called with unmatched assoc lists"
        Just yt ->
          do q <- unify [] xt yt
             case q of
               Nothing -> fundeps p q
               Just _  -> return ()) xs

  matchLeqDirect, matchLeqMap, matchPlusDirect, matchEqDirect, match :: HasCallStack => Pred -> (Pred, Evid) -> CheckM (Maybe Evid)
  match p q = matchLeqDirect p q <|> matchLeqMap p q <|> matchPlusDirect p q <|> matchEqDirect p q

  matchLeqDirect (PLeq y@(TRow es) z) (PLeq y'@(TRow es') z', v) =
    suppose (typesEqual z z') $
    cond (typesEqual y y')
      (return (Just v))
      (case (mapM splitLabel es, mapM splitLabel es') of
        (Just ps, Just ps') | all (`elem` map fst ps') (map fst ps) ->
          do trace "9 subset"
             forceAssocs ps (filter ((`elem` map fst ps) . fst) ps')
             return (Just v)
        _ -> return Nothing)
  matchLeqDirect (PLeq y z) (PLeq y' z', v) =
    suppose (typesEqual y y') $
    suppose (typesEqual z z') $
    return (Just v)
  matchLeqDirect _ _ = return Nothing

  refl (PLeq x y) =
    suppose (typesEqual x y) $
    return (Just VRefl)
  refl (PEq x y) =
    suppose (typesEqual x y) $
    return (Just VRefl)
  refl _ = return Nothing

  matchLeqMap p@(PLeq (TRow es) (TApp (TMapFun f) z)) q@(PLeq (TRow es') z', v) =
    suppose (typesEqual z z') $
    case (mapM splitLabel es, mapM splitLabel es') of
      (Just ps, Just ps') | sameSet (map fst ps) (map fst ps') ->
        do trace $ "1 match: (" ++ show p ++ ") (" ++ show q ++ ")"
           forceAssocs ps (map (second (TApp f)) ps')
           return (Just v)  -- TODO: really?
      _ -> return Nothing
  matchLeqMap _ _ = return Nothing

  matchPlusDirect p@(PPlus x y z) (q@(PPlus x' y' z'), v) =
    (trace $ "mpd" ++ show p ++ ", " ++ show q) >>
    suppose (typesEqual z z')
      (suppose (typesEqual x x') (forceFD y y') <|>
       suppose (typesEqual y y') (forceFD x x') <|>
       (case (x, x') of
          (TRow xr, TRow xr')
            | Just xs <- mapM splitLabel xr, Just xs' <- mapM splitLabel xr', sameSet (map fst xs) (map fst xs') ->
                do forceAssocs xs xs'
                   forceFD y y'
                   return (Just v)
          _ -> return Nothing) <|>
       (case (y, y') of
          (TRow yr, TRow yr')
            | Just ys <- mapM splitLabel yr, Just ys' <- mapM splitLabel yr', sameSet (map fst ys) (map fst ys') ->
                do forceAssocs ys ys'
                   forceFD x x'
                   return (Just v)
          _ -> return Nothing)
      ) <|>
    suppose (typesEqual x x')
      (suppose (typesEqual y y') (forceFD z z') <|>
       suppose (typesEqual z z') (forceFD y y'))
    where forceFD t t' =
            do q <- unify [] t t'
               case q of
                 Nothing -> fundeps p q
                 _       -> return (Just v) -- TODO: really?
  matchPlusDirect _ _ = return Nothing

  matchEqDirect p@(PEq x y) q@(PEq x' y', v) =
    suppose (typesEqual x x') $
    suppose (typesEqual y y') $
      return (Just v)
  matchEqDirect _ _ =
    return Nothing

  -- question to self: why do I have both the `fundeps` error and the `force` error?

  fundeps p q = throwError (ErrTypeMismatchFD p q)

  expand1 :: (Pred, Evid) -> [(Pred, Evid)]
  expand1 (PPlus x y z, v)
    | not (isComplement x) && not (isComplement y) =
        [(PLeq x z, VPlusLeqL v), (PLeq y z, VPlusLeqR v), (PEq x (TCompl z y), VEqPlusComplL v),
         (PEq y (TCompl z x), VEqPlusComplR v)]
    | otherwise =
        []
  expand1 (PLeq x y, v)
    | not (isComplement x) = [(PLeq (TCompl y x) y, VComplLeq v), (PPlus x (TCompl y x) y, VPlusComplR v), (PPlus (TCompl y x) x y, VPlusComplL v)]
    | otherwise            = []
  expand1 (PEq x y, VEqSym {}) = []
  expand1 (PEq x y, v) = [(PEq y x, VEqSym v)]

  isComplement (TCompl {}) = True
  isComplement _           = False

  expand2 :: (Pred, Evid) -> (Pred, Evid) -> [(Pred, Evid)]
  expand2 (PLeq x y, v1) (PLeq z w, v2)
    | y == z = [(PLeq x w, VTrans v1 v2)]
    | x == w = [(PLeq z y, VTrans v2 v1)]
  expand2 _ _ = []

  expandAll :: [(Pred, Evid)] -> [(Pred, Evid)]
  expandAll = go [] where
    go qs [] = qs
    go qs (p : ps) = go (p : qs) (ps' ++ ps) where
      ps' = expand1 p ++ concatMap (expand2 p) qs

  byAssump [] p = return Nothing
  byAssump (a : as) p = match p a <|> byAssump as p

  force p t u =
    do q <- unify [] t u
       case q of
         Nothing -> fundeps p Nothing
         Just q  -> return ()

  prim p@(PLeq (TRow y) (TRow z))
    | Just yd <- mapM label y, Just zd <- mapM label z =
      case sequence [elemIndex e zd | e <- yd] of
        Nothing -> return Nothing
        Just is ->
          do mapM_ (\(i, TLabeled _ t) -> let TLabeled _ u = z !! i in force p t u) (zip is y)
             return (Just (VLeqSimple is))
  prim (PPlus (TRow x) (TRow y) (TRow z))
    | Just xd <- mapM label x, Just yd <- mapM label y, Just zd <- mapM label z
    , length xd + length yd == length zd, sameSet (xd ++ yd) zd =
        case sequence [(Left <$> elemIndex e xd) `mplus` (Right <$> elemIndex e yd) | e <- zd] of
          Nothing -> return Nothing
          Just is ->
            do mapM_ align (zip is z)
               return (Just (VPlusSimple is))
    where align (Left i, TLabeled _ t) = force p t u where TLabeled _ u = x !! i
          align (Right i, TLabeled _ t) = force p t u where TLabeled _ u = y !! i
  prim p@(PPlus (TRow x) y (TRow z))
    | Just xs <- mapM splitLabel x, Just zs <- mapM splitLabel z, Just is <- mapM (flip elemIndex (map fst zs)) (map fst xs) =
        do forceAssocs xs (map (zs !!) is)
           let js = [j | j <- [0..length zs - 1], j `notElem` is]
               ys = (map (uncurry TLabeled . (zs !!)) js)
           trace $ "to solve " ++ show p ++ ": " ++ show y ++ " ~ " ++ show (TRow ys)
           force p y (TRow ys)
           return (Just (VPlusSimple (map Left is ++ map Right js)))
  prim p@(PPlus x (TRow y) (TRow z))
    | Just ys <- mapM splitLabel y, Just zs <- mapM splitLabel z, Just js <- mapM (flip elemIndex (map fst zs)) (map fst ys) =
        do forceAssocs ys (map (zs !!) js)
           let is = [i | i <- [0..length zs - 1], i `notElem` js]
               xs = (map (uncurry TLabeled . (zs !!)) is)
           trace $ "to solve " ++ show p ++ ": " ++ show x ++ " ~ " ++ show (TRow xs)
           force p x (TRow xs)
           return (Just (VPlusSimple (map Left is ++ map Right js)))
  prim p@(PPlus (TRow x) (TRow y) z)
    | Just xs <- mapM splitLabel x, Just ys <- mapM splitLabel y, all (`notElem` map fst xs) (map fst ys), all (`notElem` map fst ys) (map fst xs) =
        do force p z (TRow (x ++ y))
           return (Just (VPlusSimple ([Left i | i <- [0..length xs - 1]] ++ [Right (length xs + j) | j <- [0..length ys - 1]])))
  prim (PEq t u) =
    unifyProductive [] t u
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

  mapFunApp as p@(PLeq (TApp (TMapFun f) y) (TApp (TMapFun f') z)) =
    do force p f f'
       fmap (VLeqLiftL f) <$> everything as (PLeq y z)
  mapFunApp as p@(PLeq (TRow []) (TApp (TMapFun f) z)) =
    fmap (VLeqLiftL f) <$> everything as (PLeq (TRow []) z)
  mapFunApp as p@(PLeq (TRow y) (TApp (TMapFun f) z))
    | TLam v (Just k) (TVar i w _) <- f  -- I think this case should actually have been normalized away....
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel y =
      fmap (VPredEq (VEqLeq (VEqMap `VTrans` VEqRow [ VEqSym VEqBeta | t <- ts]) VRefl) .
            VLeqLiftL f) <$> everything as (PLeq (TRow y) z)
  mapFunApp as p@(PLeq (TApp (TMapFun f) y) (TRow [])) =
    fmap (VLeqLiftL f) <$> everything as (PLeq y (TRow []))
  mapFunApp as p@(PLeq (TApp (TMapFun f) y) (TRow z))
    | Just (ls, fs, es) <- funCallsFrom z =
      do mapM_ (force p f) fs
         fmap (VLeqLiftL f) <$> everything as (PLeq y (TRow (zipWith TLabeled ls es)))
    | TLam v (Just k) (TVar i w _) <- f
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel z =
      fmap (VPredEq (VEqLeq VRefl (VEqMap `VTrans` VEqRow [ VEqSym VEqBeta | t <- ts])) .
            VLeqLiftL f) <$> everything as (PLeq y (TRow z))
  mapFunApp as p@(PPlus (TApp (TMapFun f) x) (TApp (TMapFun g) y) (TApp (TMapFun h) z)) =
    do force p f g
       force p g h
       fmap (VPlusLiftL f) <$> everything as (PPlus x y z)
  mapFunApp _ _ = return Nothing

loop :: [Problem] -> CheckM ()
loop [] = return ()
loop ps =
  do (b, ps') <- once False [] ps
     if b
     then loop ps'
     else throwError . ErrNotEntailed =<< mapM notEntailed ps'
  where once b qs [] = return (b, qs)
        once b qs (p : ps) =
          do (b', TCOut ps') <- listen $ solve p
             once (b || b')
                  (if b' then qs else p : qs)
                  (ps ++ ps')
        notEntailed (cin, p, _) =
          do p' <- flattenP p
             ps' <- mapM flattenP (pctxt cin)
             return (p', ps')

andSolve :: CheckM a -> CheckM a
andSolve m =
  censor (const (TCOut [])) $
  do (x, TCOut goals) <- listen m
     trace "-- solver start --"
     loop goals
     trace "-- solver stop --"
     return x
