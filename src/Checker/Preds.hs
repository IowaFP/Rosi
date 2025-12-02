{-# LANGUAGE ParallelListComp #-}
module Checker.Preds where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Data.Bifunctor
import Data.Either (isLeft, isRight)
import Data.IORef
import Data.List


import Checker.Monad
import Checker.Normalize
import Checker.Promote
import Checker.Types (checkPred)
import Checker.Unify
import Checker.Utils
import Printer
import Syntax

import GHC.Stack

import qualified Debug.Trace as T

solve :: HasCallStack => (TCIn, Pred, IORef (Maybe Evid)) -> CheckM Bool
solve (cin, p, r) =
  local (const cin) $
  do trace $ "Solving: " ++ show p ++ "\nin " ++ show (kctxt cin)
     as' <- mapM (normalizeP [] <=< flattenP) (pctxt cin)
     when (not (null as')) $ trace ("Expanding " ++ show as')
     let as'' = expandAll (zip as' [VVar i | i <- [0..]])
     let eqns = pickEqns as''
     when (not (null as'')) $ trace ("Expanded " ++ show as' ++ " to " ++ show as'')
     when (not (null eqns)) $ trace ("Found equations " ++ show eqns)
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
       v <- byAssump as p <|> prim p <|> refl p <|> mapFunApp as p
       trace ("Solved " ++ show p ++ " by " ++ show v)
       return v

  -- TODO: this shouldn't be necessary any longer, as labels are stored in sorted order??
  sameSet :: Eq a => [a] -> [a] -> Bool
  sameSet xs ys = all (`elem` ys) xs && all (`elem` xs) ys

  allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
  allM p xs = and <$> mapM p xs

  typesEqual :: Ty -> Ty -> CheckM Bool
  typesEqual t u =
    do q <- check [] t u
       return (isRight q)

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
               Left _ -> fundeps p
               Right _  -> return ()) xs

  matchLeqDirect, matchLeqMap, matchPlusDirect, matchPlusMap, matchEqDirect, matchFoldDirect, match :: HasCallStack => Pred -> (Pred, Evid) -> CheckM (Maybe Evid)
  match p q = matchLeqDirect p q <|> matchLeqMap p q <|> matchPlusDirect p q <|> matchPlusMap p q <|> matchEqDirect p q <|> matchFoldDirect p q

  matchLeqDirect (PLeq y@(TRow es) z) (PLeq y'@(TRow es') z', v) =
    suppose (typesEqual z z') $
    cond (typesEqual y y')
      (return (Just v))
      (case (mapM label es, mapM label es') of
         (Just ed, Just ed')
            | Just is <- sequence [elemIndex e ed' | e <- ed] ->
               do mapM_ (\(i, TLabeled _ t) -> let TLabeled _ u = es' !! i in force p t u)
                        (zip is es)
                  return (Just (VLeqSimple is `VLeqTrans` v))
         _ -> return Nothing)
  matchLeqDirect (PLeq y z) (PLeq y' z', v) =
    suppose (typesEqual y y') $
    suppose (typesEqual z z') $
    return (Just v)
  matchLeqDirect _ _ = return Nothing

  refl (PLeq x y) =
    suppose (typesEqual x y) $
    return (Just VLeqRefl)
  refl _ = return Nothing

  matchLeqMap p@(PLeq (TRow es) (TApp (TMapFun f) z)) q@(PLeq (TRow es') z', v) =
    suppose (typesEqual z z') $
    case (mapM label es, mapM label es') of
      (Just ed, Just ed')
         | Just is <- sequence [elemIndex e ed' | e <- ed] ->
            do mapM_ (\(i, TLabeled _ t) -> let TLabeled _ u = es' !! i in force p t (TApp f u))
                     (zip is es)
               return (Just (VLeqSimple is `VLeqTrans` v))
      _ -> return Nothing
  matchLeqMap _ _ = return Nothing

  matchPlusDirect p@(PPlus x y z) (q@(PPlus x' y' z'), v) =
    (trace $ "mpd " ++ show p ++ ", " ++ show q) >>
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
                 Left _ -> fundeps p
                 _       -> return (Just v)
  matchPlusDirect _ _ = return Nothing

  {-

  matchPlusMap handles the following case:
    Given p@(PPlus x y z) q@(PPlus x' y' z') such that
      - ONE of x, y, z should be a f* x', f* y', or f* z'
      - ANOTHER of x, y, z should be a concrete row { l1 := t1, ... }
      - the CORRESPONDING x', y', z' is a concrete row { l1 := t1', ...}
    We solve the constraint requiring that:
      - each of the ti' ~ f ti
      - the REMAINING x, y, z is f* x', f* y', or f* z'

  Now, this case can arise 6 different ways, so I've abstracted the meat to the
  `align` case, in which the FIRST is `z` and the second is `x`. We then call
  the `align` case for each permutation of the input rows.

  -}

  matchPlusMap p@(PPlus x y z) (q@(PPlus x' y' z'), v) =
    trace ("mpm " ++ show p ++ ", " ++ show q) >>
    (align x y z x' y' z' v <|>
     align y x z y' x' z' v <|>
     align y z x y' z' x' v <|>
     align z y x z' y' x' v <|>
     align x z y x' z' y' v <|>
     align z x y z' x' y' v)
    where align x y z x' y' z' v
            | TApp (TMapFun zf) zr <- z =
              suppose (typesEqual zr z') $
              (case (x, x') of
                (TRow xr, TRow xr')
                   | Just xs <- mapM splitLabel xr, Just xs' <- mapM splitLabel xr', sameSet (map fst xs) (map fst xs') ->
                       do forceAssocs xs (map (second (TApp zf)) xs')   -- Is this actually forced?
                          forceFD y (TApp (TMapFun zf) y')
                          return (Just (VPlusLiftL zf v))
                   | otherwise -> trace ("mpm failed: " ++ show xr ++ ", " ++ show xr') >>
                                  return Nothing
                _ -> return Nothing)
            | otherwise = return Nothing

          forceFD t t' =
            do q <- unify [] t t'
               case q of
                 Left _  -> fundeps p
                 Right _ -> return (Just v)
  matchPlusMap _ _ = return Nothing

  matchEqDirect p@(PEq x y) q@(PEq x' y', v) =
    suppose (typesEqual x x') $
    suppose (typesEqual y y') $
      return (Just v)
  matchEqDirect _ _ =
    return Nothing

  matchFoldDirect p@(PFold z) q@(PFold z', v) =
    suppose (typesEqual z z') $
      return (Just v)
  matchFoldDirect _ _ =
    return Nothing

  -- question to self: why do I have both the `fundeps` error and the `force` error?

  fundeps p = throwError (ErrTypeMismatchFD p)

  expand1 :: (Pred, Evid) -> [(Pred, Evid)]
  expand1 (PPlus x y z, v)
    | not (isComplement x) && not (isComplement y) =
        [(PLeq x z, VPlusLeqL v), (PLeq y z, VPlusLeqR v), (PEq x (TCompl z y), VEqPlusComplL v),
         (PEq y (TCompl z x), VEqPlusComplR v)]
    | otherwise =
        []
  expand1 (PLeq x y, v) = compls ++ subrows
    where compls
            | not (isComplement x) = [(PLeq (TCompl y x) y, VComplLeq v), (PPlus x (TCompl y x) y, VPlusComplR v), (PPlus (TCompl y x) x y, VPlusComplL v)]
            | otherwise            = []
          subrows
            | TRow fs <- x, length fs > 1, not (isLiteralRow y) =
              let is = [0..length fs - 1]
                  subsets = [filter (i /=) is | i <- is]
                  evids = [(PLeq (TRow (map (fs !!) is)) y, VLeqTrans (VLeqSimple is) v) | is <- subsets, not (null is)]
              in evids
            | otherwise = []
          isLiteralRow (TRow {}) = True
          isLiteralRow _         = False
  expand1 (PEq x y, VEqSym {}) = []
  expand1 (PEq x y, v) = [(PEq y x, VEqSym v)]
  expand1 (PFold _, _) = []

  isComplement (TCompl {}) = True
  isComplement _           = False

  expand2 :: (Pred, Evid) -> (Pred, Evid) -> [(Pred, Evid)]
  expand2 (PLeq x y, v1) (PLeq z w, v2)
    | y == z = [(PLeq x w, VLeqTrans v1 v2)]
    | x == w = [(PLeq z y, VLeqTrans v2 v1)]
  expand2 _ _ = []

  expandAll :: [(Pred, Evid)] -> [(Pred, Evid)]
  expandAll = go [] where
    go qs [] = reverse qs
    go qs (p : ps) =
      go (p : qs) (ps' ++ ps) where
      seen = map fst (qs ++ ps)
      ps' = filter ((`notElem` seen) . fst) (expand1 p ++ concatMap (expand2 p) qs)

  byAssump [] p = return Nothing
  byAssump (a : as) p = match p a <|> byAssump as p

  force p t u =
    do q <- unify [] t u
       case q of
         Left _ -> fundeps p
         Right _  -> return ()

  prim p@(PLeq (TRow y) (TRow z))
    | Just yd <- mapM concreteLabel y, Just zd <- mapM concreteLabel z =
      do case sequence [elemIndex e zd | e <- yd] of
           Nothing -> return Nothing
           Just is ->
             do mapM_ (\(i, TLabeled _ t) -> let TLabeled _ u = z !! i in force p t u) (zip is y)
                return (Just (VLeqSimple is))
  prim (PPlus (TRow x) (TRow y) (TRow z))
    | Just xd <- mapM concreteLabel x, Just yd <- mapM concreteLabel y, Just zd <- mapM concreteLabel z
    , length xd + length yd == length zd, sameSet (xd ++ yd) zd =
        case sequence [(Left <$> elemIndex e xd) `mplus` (Right <$> elemIndex e yd) | e <- zd] of
          Nothing -> return Nothing
          Just is ->
            do mapM_ align (zip is z)
               return (Just (VPlusSimple is))
    where align (Left i, TLabeled _ t) = force p t u where TLabeled _ u = x !! i
          align (Right i, TLabeled _ t) = force p t u where TLabeled _ u = y !! i
  prim p@(PPlus (TRow x) y (TRow z))
    | Just xs <- mapM splitConcreteLabel x, Just zs <- mapM splitConcreteLabel z, Just is <- mapM (flip elemIndex (map fst zs)) (map fst xs) =
        do forceAssocs xs (map (zs !!) is)
           let js = [j | j <- [0..length zs - 1], j `notElem` is]
               ys = (map (uncurry (TLabeled . TLab) . (zs !!)) js)
               go n m
                 | n >= length zs = []
                 | Just i <- elemIndex n is = Left i : go (n + 1) m
                 | otherwise = Right m : go (n + 1) (m + 1)
           trace $ "to solve " ++ show p ++ ": " ++ show y ++ " ~ " ++ show (TRow ys)
           force p y (TRow ys)
           return (Just (VPlusSimple (go 0 0)))
  prim p@(PPlus x (TRow y) (TRow z))
    | Just ys <- mapM splitConcreteLabel y, Just zs <- mapM splitConcreteLabel z, Just js <- mapM (flip elemIndex (map fst zs)) (map fst ys) =
        do forceAssocs ys (map (zs !!) js)
           let is = [i | i <- [0..length zs - 1], i `notElem` js]
               xs = (map (uncurry (TLabeled . TLab) . (zs !!)) is)
               go n m
                 | n >= length zs = []
                 | Just j <- elemIndex n js = Right j : go (n + 1) m
                 | otherwise = Left m : go (n + 1) (m + 1)
           trace $ "to solve " ++ show p ++ ": " ++ show x ++ " ~ " ++ show (TRow xs)
           force p x (TRow xs)
           return (Just (VPlusSimple (go 0 0)))
  prim p@(PPlus (TRow x) (TRow y) z)
    | Just xs <- mapM splitConcreteLabel x, Just ys <- mapM splitConcreteLabel y, all (`notElem` map fst xs) (map fst ys), all (`notElem` map fst ys) (map fst xs) =
        let zs = sortOn fst (xs ++ ys)
            pick k =
              case (elemIndex k (map fst xs), elemIndex k (map fst ys)) of
                (Just i, _) -> Left i
                (_, Just j) -> Right j
            is = map (pick . fst) zs
        in
        do force p z (TRow (map (uncurry (TLabeled . TLab)) zs))
           return (Just (VPlusSimple is))
  prim p@(PEq t u) =
    do result <- unifyProductive [] t u
       case result of
         Productive v -> return (Just v)
         Unproductive -> return Nothing
         UnificationFails _ -> throwError (ErrTypeMismatchPred p t u)
  prim p@(PFold (TRow xs)) =
    return (Just (VFold (length xs)))
  prim _ = return Nothing

  funCallsFrom :: [Ty] -> Maybe ([Ty], [Ty], [Ty])
  funCallsFrom z
    | Just ls <- mapM label z
    , Just ts <- mapM labeled z
    , Just (fs, es) <- mapAndUnzipM tyAppFrom ts = return (ls, fs, es)
    | otherwise                                  = Nothing
    where tyAppFrom (TApp f e) = Just (f, e)
          tyAppFrom _          = Nothing

  defer :: Pred -> CheckM (Maybe Evid)
  defer p =
    do r <- newRef Nothing
       require p r
       name <- fresh "g"
       return (Just (VGoal (Goal (name, r))))

  mapFunApp as p@(PLeq (TApp (TMapFun f) y) (TApp (TMapFun f') z)) =
    suppose (typesEqual f f') $
      fmap (VLeqLiftL f) <$> defer (PLeq y z)
  mapFunApp as p@(PLeq (TRow []) (TApp (TMapFun f) z)) =
    fmap (VLeqLiftL f) <$> defer (PLeq (TRow []) z)
  mapFunApp as p@(PLeq (TApp (TMapFun f) y) (TRow [])) =
    fmap (VLeqLiftL f) <$> defer (PLeq y (TRow []))
  mapFunApp as p@(PLeq (TApp (TMapFun f) y) (TRow z))
    | Just (ls, fs, es) <- funCallsFrom z =
    suppose (allM (typesEqual f) fs) $
      fmap (VLeqLiftL f) <$> defer (PLeq y (TRow (zipWith TLabeled ls es)))
  mapFunApp as p@(PPlus x (TApp (TMapFun f) y) (TApp (TMapFun g) z)) =
    suppose (typesEqual f g) $
    do x' <- typeGoal' "x" =<< kindOf y
       force p x (TApp (TMapFun f) x') -- I am very unsure about this
       fmap (VPlusLiftL f) <$> defer (PPlus x' y z)
  mapFunApp as p@(PPlus (TApp (TMapFun f) x) y (TApp (TMapFun g) z)) =
    suppose (typesEqual f g) $
    do y' <- typeGoal' "y" =<< kindOf x
       force p y (TApp (TMapFun f) y') -- I am very unsure about this
       fmap (VPlusLiftL f) <$> defer (PPlus x y' z)
  mapFunApp as p@(PPlus (TApp (TMapFun f) x) (TApp (TMapFun g) y) z) =
    suppose (typesEqual f g) $
    do z' <- typeGoal' "z" =<< kindOf x
       force p z (TApp (TMapFun f) z') -- I am very unsure about this
       fmap (VPlusLiftL f) <$> defer (PPlus x y z')
  mapFunApp _ _ = return Nothing

guess :: [Problem] -> CheckM (Maybe [Problem])
guess (pr@(tcin, PEq t u, v) : prs) =
  local (const tcin) $
  do t' <- fst <$> normalize [] t
     u' <- fst <$> normalize [] u
     case (t', u') of
       (TInst (Unknown {}) (TInst (Unknown _ (Goal (s, r))) _), _) ->
         do trace $ unwords ["guessing", s, ":= {}"]
            writeRef r (Just (Known []))
            return (Just (pr : prs))
       (_, TInst (Unknown {}) (TInst (Unknown _ (Goal (s, r))) _)) ->
           do trace $ unwords ["guessing", s, ":= {}"]
              writeRef r (Just (Known []))
              return (Just (pr : prs))
       (u@(TInst (Unknown {}) _), t@(TForall {})) ->
          guessInstantiation t u
       (t@(TForall {}), u@(TInst (Unknown {}) _)) ->
          guessInstantiation t u
       (t@(TApp (TUnif v) t'), u) ->
          do x <- fresh "x"
             k <- kindOf t'
             u' <- TLam x (Just k) <$> walk (TVar 0 [x, ""]) t' 0 u
             trace $
               "solving " ++ show (PEq t u) ++ ":\n" ++
               "by guessing " ++ show v ++ " := " ++ show u'
             solveUV v u'
             return (Just (pr : prs))
       (u, t@(TApp (TUnif v) t')) ->
          do x <- fresh "x"
             k <- kindOf t'
             u' <- TLam x (Just k) <$> walk (TVar 0 [x, ""]) t' 0 u
             trace $
               "solving " ++ show (PEq t u) ++ ":\n" ++
               "by guessing " ++ show v ++ " := " ++ show u'
             solveUV v u'
             return (Just (pr : prs))
       _ -> fmap (pr :) <$> guess prs

  where -- There is a lot of similarity with the code in unifyInstantiating here...
        -- Assuming t starts with quantifiers, `u` starts with unknown instantiation
        guessInstantiation t (TInst (Unknown n (Goal (s, r))) u) =
          do xs' <- mapM fresh xs
             refs <- replicateM (length xs) (newRef Nothing)
             l <- theLevel
             let us = [TUnif (UV 0 l (Goal (x, r)) k) | x <- xs' | r <- refs | k <- ks ]
             writeRef r (Just (Known (map TyArg us)))
             t''' <- instantiate t us
             trace $ unlines [ unwords ["guessing", s, ":=", show us]
                             , unwords ["refined goal to", show (PEq t''' u)] ]
             return (Just ((tcin, PEq t''' u, v) : prs))

          where (qus, t') = quants t
                foralls = takeWhile isForall qus
                (xs, ks) = unzip [(x, k) | QuForall x k <- foralls]
                t'' = quantify (drop (length foralls) qus) t'

                isForall (QuForall {}) = True
                isForall _             = False

                instantiate t [] = return t
                instantiate (TForall _ _ t) (u : us) =
                  do t' <- shiftTN 0 (-1) <$> subst 0 (shiftTN 0 1 u) t
                     instantiate t' us


        -- `walk x u m t` builds the body of a function that, applied to `u`,
        -- returns `t`. There are a couple of pieces:
        --
        --  * If we find `u` inside `t`, we want to use the variable, not the
        --    constant type `t`. (Of course both are valid... we are guessing!)
        --    The parameter `x` carries the type variable to use in this case
        --
        --  * Otherwise, we need to shift (because this will be the body of a
        --    new function). Because we are shifting, we need to carry around a
        --    minimum index.
        --
        --  * We might as well flatten uvars as we go.
        --
        --  * Oops, when we shift, we also need to shift the type `u` that we're
        --    looking for.
        --
        -- I think that's all the concerns for now.
        walk :: Ty -> Ty -> Int -> Ty -> CheckM Ty
        walk x u m t
          | u == t = return x
        walk x u m (TVar n s)
          | n < m = return (TVar n s)
          | otherwise = return (TVar (n + 1) s)
        walk x u m (TUnif v) =
          do mt <- readRef (goalRef (uvGoal v))
             case mt of
               Nothing -> return (TUnif v { uvShift = uvShift v + 1 })
               Just t  -> walk x u m (shiftTN 0 (uvShift v) t)
        walk _ _ _ TFun = return TFun
        walk x u m (TThen p t) = TThen <$> walkP x u m p <*> walk x u m t
        walk x u m (TForall s mk t) = TForall s mk <$> walk (shiftTN 0 1 x) (shiftTN 0 1 u) (m + 1) t
        walk x u m (TLam s mk t) = TLam s mk <$> walk (shiftTN 0 1 x) (shiftTN 0 1 u) (m + 1) t
        walk x u m (TApp t t') = TApp <$> walk x u m t <*> walk x u m t'
        walk x u m t@(TLab _) = return t
        walk x u m (TSing t) = TSing <$> walk x u m t
        walk x u m (TLabeled l t) = TLabeled <$> walk x u m l <*> walk x u m t
        walk x u m (TRow ts) = TRow <$> mapM (walk x u m) ts
        walk x u m (TConApp k t) = TConApp k <$> walk x u m t
        walk x u m (TMapFun f) = TMapFun <$> walk x u m t
        walk x u m (TCompl t t') = TCompl <$> walk x u m t <*> walk x u m t'
        walk x u m (TMapArg r) = TMapArg <$> walk x u m r
        walk x u m (TInst is t) = TInst <$> walkIs is <*> walk x u m t where
          walkIs (Known is) = Known <$> mapM walkI is
          walkIs (Unknown n g) =
            do mis <- readRef (goalRef g)
               case mis of
                 Nothing -> return (Unknown n g)
                 Just is' -> walkIs (shiftIsV [] 0 n is')
          walkI (TyArg t) = TyArg <$> walk x u m t
          walkI (PrArg v) = return (PrArg v)

        walkP :: Ty -> Ty -> Int -> Pred -> CheckM Pred
        walkP v u m (PLeq x y)    = PLeq <$> walk v u m x <*> walk v u m y
        walkP v u m (PEq t t')    = PEq <$> walk v u m t <*> walk v u m t'
        walkP v u m (PPlus x y z) = PPlus <$> walk v u m x <*> walk v u m y <*> walk v u m z


guess (pr : prs) = fmap (pr :) <$> guess prs
guess [] = return Nothing

solverLoop :: [Problem] -> CheckM [Problem]
solverLoop [] = return []
solverLoop ps =
  do trace $ unlines $ "Solver loop:" : ["    " ++ renderString (ppr p) | (_, p, _) <- ps]
     (b, ps') <- once False [] ps
     if b
     then solverLoop ps'
     else do mps <- guess ps'
             case mps of
               Just ps'' -> solverLoop ps''
               Nothing -> trace "Solver done" >> return ps'
  where once b qs [] = return (b, qs)
        once b qs (p : ps) =
          do (b', TCOut ps') <- collect $ solve p
             once (b || b')
                  (if b' then qs else p : qs)
                  (ps ++ ps')

andSolve :: CheckM a -> CheckM a
andSolve m =
  censor (const (TCOut [])) $
  do (x, TCOut goals) <- collect m
     remaining <- solverLoop goals
     if null remaining
     then return x
     else notEntailed remaining

notEntailed :: [Problem] -> CheckM a
notEntailed problems = throwError . ErrNotEntailed =<< mapM mkError problems
  where mkError (cin, p, _) =
          do p' <- flattenP p
             ps' <- mapM flattenP (pctxt cin)
             return (p', ps')


