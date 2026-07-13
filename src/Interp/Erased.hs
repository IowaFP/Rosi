module Interp.Erased where

import Data.IORef
import Data.List        (intercalate)
import Data.Maybe       (fromMaybe)
import Debug.Trace      qualified as T
import GHC.Stack
import Printer
import Syntax
import System.IO.Unsafe

{-# NOINLINE traceEvaluation #-}
traceEvaluation :: IORef Bool
traceEvaluation = unsafePerformIO (newIORef False)

trace s x =
  if unsafePerformIO (readIORef traceEvaluation)
    then T.trace s x
    else x

type Env = ([EValue], [Value])

data Body = Term Term | Prim (Env -> Value)

instance Show Body where
  show (Term t) = renderString (ppr t)
  show (Prim _) = "<<prim>>"

data Value
  = VPrLam Env Body
  | VLam Env Body
  | VSing (Maybe String)
  | VVariant Int Value (Maybe String)
  | VRecord [Value] [Maybe String]
  | VSyn (Int -> Value)
  | VString String

-- Alias for Unit (as implemented in Base)
vUnit :: Value
vUnit = VRecord [] []

-- Convert a Bool to its Ro.Base implementation
-- type Bool : *
-- type Bool = Sigma { 'True := Unit, 'False := Unit }
fromBool :: Bool -> Value
fromBool False = VVariant 0 vUnit (Just "False")
fromBool True  = VVariant 1 vUnit (Just "True")

instance FromPeano Value where
  fromPeano :: Value -> Maybe Int
  fromPeano (VVariant _ p (Just "Succ"))               = fmap (+ 1) (fromPeano p)
  fromPeano (VVariant _ (VRecord [] []) (Just "Zero")) = Just 0
  fromPeano _                                          = Nothing

listFromVariant :: Value -> Maybe [String]
-- Match on names = ["1", "2"]
listFromVariant (VVariant _ (VRecord [x, xs] _) (Just "Cons")) = case listFromVariant xs of
  Nothing -> Nothing
  Just ys -> Just (show x : ys)
listFromVariant (VVariant _ (VRecord [] []) (Just "Nil")) = Just []
listFromVariant _ = Nothing

showRecordEntry :: Show v => Maybe String -> v -> Int -> String
showRecordEntry k v i = fromMaybe (show i) k ++ ": " ++ show v

isTuple :: [Maybe String] -> Bool
isTuple names = and [s == Just (show n) | (s, n) <- zip names [1..]]

showTuple :: [Value] -> String
showTuple vs = "(" ++ intercalate ", " (map show vs) ++ ")"

instance Show Value where
  show (VPrLam _ b) = "\\p " ++ show b
  show (VLam _ b) = "\\ " ++ show b
  show (VSing (Just s)) = s
  show (VSing Nothing) = "<<unknown>>"
  -- Special cases
  show (VVariant k w l)
    -- lists
    | Just [] <- listFromVariant (VVariant k w l) = "List{}"
    | Just ss <- listFromVariant (VVariant k w l) = "List{\n  " ++ intercalate ", \n  " ss ++ "\n}"
    -- Nats
    | Just n <- fromPeano (VVariant k w l) = show n
    -- label present and mapped to Unit. e.g. Bool, Nothing. Check after previous cases so it won't match Zero or Nil
    | (VRecord [] [], Just s) <- (w, l) = s
    | otherwise = "[" ++ fromMaybe (show k) l ++ ": " ++ show w ++ "]"
  show (VRecord vs names) | isTuple names = showTuple vs
  show (VRecord vs names) = "⟨" ++ intercalate ", " (zipWith3 showRecordEntry names vs [0..]) ++ "⟩"
  show (VSyn t) = "<<syn>>"
  show (VString s) = "\"" ++ s ++ "\""

--------------------------------------------------------------------------------
-- Evidence
--
-- An evidence list is either a list of included indices or a list of excluded
-- indices. We use the same representation for (+) evidence, where the included
-- denote the cases on the left and the excluded denote the cases on the right.

data EList = Incl [Int] | Excl [Int]
  deriving (Show)

dual :: EList -> EList
dual (Incl is) = Excl is
dual (Excl is) = Incl is

-- Translate from `EList` representation to picks, needed for branching and
-- concatenation. This will always be an unbounded list: if the evidence is
-- `Incl`, we don't know how many to pick on the right; if the evidence is
-- `Excl`, we don't know how many to pick from the left.

picks :: EList -> [Either Int Int]
picks es | Incl is <- es = go 0 0 0 is Left Right
         | Excl is <- es = go 0 0 0 is Right Left
  where -- The idea here is that we are counting up the positions in the return
        -- list `n`, determining which positions come from the "left" and
        -- "right" inputs. `l` and `r` track positions in the "left" and "right"
        -- input lists.
        go n l r [] left right = right r : go (n + 1) l (r + 1) [] left right
        go n l r (m : ms) left right
          | n == m = left l : go (n + 1) (l + 1) r ms left right
          | otherwise = right r : go (n + 1) l (r + 1) (m : ms) left right

-- Computes the included cases. If the input evidence is an exclusion list, this
-- will be infinite.
included :: EList -> [Int]
included (Incl is) = is
included (Excl is) = filter (`notElem` is) [0..]

-- picks the n'th element *included*
(<!>) :: EList -> Int -> Int
es <!> n = included es !! n

data EValue = VLeq EList | VPlus EList | VEq | VVFold Int
  deriving (Show)

evalB :: Env -> Body -> Value
evalB h (Term e) = eval h e
evalB h (Prim f) = f h

app :: Value -> Value -> Value
app (VLam (hp, he) f') v = evalB (hp, v : he) f'
app v w                  = error $ "don't know how to apply " ++ show v ++ " to " ++ show w

prapp :: Value -> EValue -> Value
prapp f@(VPrLam (hp, he) f') v =
  evalB (v : hp, he) f'
prapp f v =
  error $ "don't know how to apply " ++ show f ++ " to " ++ show v

recordFrom :: (HasCallStack) => Value -> Int -> (Value, Maybe String)
recordFrom (VRecord vs names) i = (vs !! i, names !! i)
recordFrom (VSyn f) i           = (f i, Nothing)
recordFrom v _                  = (v, Nothing)

recordSize :: (HasCallStack) => Value -> Int
recordSize (VRecord vs _) = length vs
recordSize (VSyn f)       = error "unbounded"
recordSize v              = 1

variantFrom :: (HasCallStack) => Value -> (Int, Value, Maybe String)
variantFrom (VVariant k v s) = (k, v, s)
variantFrom v                = (0, v, Just "Test")

labelFromValue :: Value -> Maybe String
labelFromValue (VSing t) = t
labelFromValue _         = Nothing

labelFromTy :: Ty -> Maybe String
labelFromTy (TLab s) = Just s
labelFromTy _        = Nothing

eval, eval' :: (HasCallStack) => Env -> Term -> Value
eval h e =
  trace ("Eval: " ++ renderString (ppr e)) $
  eval' h e
eval' (_, he) (EVar i _)
  | i < length he = he !! i
  | otherwise = error $ "environment too small for variable " ++ show i ++ ": " ++ show he
eval' h (ELam _ _ e) = VLam h (Term e)
eval' h (EApp f e) = app (eval h f) (eval h e)
eval' h (ELet x e f) = eval h (EApp (ELam x Nothing f) e)
eval' h (ETyLam _ _ e) = eval h e
eval' h (EPrLam _ e) = VPrLam h (Term e)
eval' h (EInst t (Known is)) = inst (eval h t) is
  where
    inst v []             = v
    inst v (TyArg _ : is) = inst v is
    inst v (PrArg q : is) = inst (prapp v (evalV h q)) is
eval' h (ESing t) = VSing (labelFromTy t)
eval' h (ELabel (Just k) l e) =
  case k of
    Pi       -> VRecord [v]  [labelFromValue (eval h l)]
    Sigma    -> VVariant 0 v (labelFromValue (eval h l))
    TCUnif _ -> VRecord [v]  [labelFromValue (eval h l)]
  where
    v = eval h e
eval' h e0@(EUnlabel (Just k) e l) =
  case (k, v) of
    (Sigma, VVariant _ v _) -> v
    (Pi, VRecord [v] _)     -> v
    (Pi, VSyn f)            -> f 0
  where
    v = eval h e
eval' h (EConst CPrj) =
  VPrLam h $ Prim $ \h ->
    VLam h $ Prim $ \case
      (VLeq (Incl is) : _, VSyn f : _) ->
        VRecord (map f is) (replicate  (length is) Nothing)
      (VLeq es@(Excl {}) : _, VSyn f : _) ->
        VSyn (\i -> f (es <!> i))
      (VLeq (Incl is) : _, VRecord vs vNames : _) ->
        let (values, names) = unzip (map (zip vs vNames !!) is)
        in VRecord values names
      (VLeq (Excl is) : _, VRecord vs vNames : _) ->
        let (names, values) = unzip (map snd $ filter ((`notElem` is) . fst) (zip [0..] (zip vs vNames)))
        in VRecord names values
      _ -> error $ "bad environment for prj: " ++ show h
eval' h (EConst CInj) =
  -- VPrLam h (Value (VLam h (Const CPrj)))
  VPrLam h $ Prim $ \h ->
    VLam h $ Prim $ \case
      (VLeq is : _, v : _) ->
        let (k, w, s) = variantFrom v
         in VVariant (is <!> k) w s
      _ -> error $ "bad environment for inj: " ++ show h
eval' h (EConst CConcat) =
  VPrLam h $ Prim $ \h ->
    VLam h $ Prim $ \h ->
      VLam h $ Prim $ \case
        (VPlus es : _, VRecord ws wNames : VRecord vs vNames : _) ->
          let ps = picks es
              pick (Left i)  = (vs !! i, vNames !! i)
              pick (Right j) = (ws !! j, wNames !! j)
          in uncurry VRecord (unzip [pick i | i <- take (length vs + length ws) ps])
        (VPlus es@(Incl is) : _, VRecord ws wNames : v : _) ->
          let ps = picks es
              pick (Left i)  = recordFrom v i
              pick (Right j) = (ws !! j, wNames !! j)
          in uncurry VRecord (unzip [pick i | i <- take (length is + length ws) ps])
        (VPlus es@(Excl is) : _, w : VRecord vs vNames : _) ->
          let ps = picks es
              pick (Left i)  = (vs !! i, vNames !! i)
              pick (Right j) = recordFrom w j
          in uncurry VRecord (unzip [pick i | i <- take (length is + length vs) ps])
        (VPlus es : _, w : v : _) ->
          let ps = picks es
              pick (Left i)  = recordFrom v i
              pick (Right j) = recordFrom w j
          in VSyn (fst . pick . (ps !!))
eval' h (EConst CBranch) =
  VPrLam h $ Prim $ \h ->
    VLam h $ Prim $ \h ->
      VLam h $ Prim $ \h ->
        VLam h $ Prim $ \case
          (VPlus is : _, v : g : f : _) ->
            let (k, w, s) = variantFrom v
             in case picks is !! k of
                  Left i  -> app f (VVariant i w s)
                  Right i -> app g (VVariant i w s)
          _ -> error $ "bad environment for branch: " ++ show h
eval' h (EConst CFix) =
  eval h (ELam "f" Nothing (EApp (EVar 0 ["f", ""]) (EApp (EConst CFix) (EVar 0 ["f", []]))))
eval' h (EConst CStringCat) =
  VLam h $ Prim $ \h ->
    VLam h $ Prim $ \case
      (_, VString s1 : VString s0 : _) ->
        VString (s0 ++ s1)
      _ -> error $ "bad environment for (^): " ++ show h
eval' h (EConst CStringEq) =
  VLam h $ Prim $ \h ->
    VLam h $ Prim $ \case
      (_, VString s1 : VString s0 : _) ->
        fromBool (s0 == s1)
      _ -> error $ "bad environment for (~): " ++ show h
eval' h (EConst CSyn) =
  VLam h $ Prim $ \h ->
    VLam h $ Prim $ \case
      (_, f : _) ->
        VSyn (\i -> app (prapp f (VLeq (Incl [i]))) (VSing Nothing))
eval' h (EConst CAna) =
  VLam h $ Prim $ \h ->
    VLam h $ Prim $ \h ->
      VLam h $ Prim $ \case
        (_, VVariant k w s : f : _) ->
          app (app (prapp f (VLeq (Incl [k]))) (VSing s)) w
        (_, v : e : _) ->
          error $ "bad argument for (ana" ++ show e ++ "): " ++ show v
eval' h (EConst CFold) =
  VPrLam h $ Prim $ \h ->
    VLam h $ Prim $ \h ->
      VLam h $ Prim $ \h ->
        VLam h $ Prim $ \h ->
          VLam h $ Prim $ \h ->
            VLam h $ Prim $ \case
              (VVFold n : _, r : def : comp : single : _) ->
                let vs = recordFrom r
                    one k = app (app (prapp single (VLeq $ Incl [k])) (VSing Nothing)) (fst (vs k))
                 in if n == 0 then def else foldl (\v w -> app (app comp v) w) (one 0) (map one [1 .. n - 1])
eval' h (ECast e q) = q `seq` eval h e
eval' h (ETyped e _) = eval h e
eval' h (EStringLit s) = VString s
eval' h e = error $ "eval' missing " ++ show e

evalV :: Env -> Evid -> EValue
evalV (hp, he) (VVar i)    = hp !! i
evalV h (VPredEq _ v)      = evalV h v
evalV h v@(VLeqRefl)       = VLeq $ evalLeq h v
evalV h v@(VLeqTrans {})   = VLeq $ evalLeq h v
evalV h v@(VLeqSimple {})  = VLeq $ evalLeq h v
evalV h v@(VLeqLiftL {})   = VLeq $ evalLeq h v
evalV h v@(VLeqLiftR {})   = VLeq $ evalLeq h v
evalV h v@(VPlusLeqL {})   = VLeq $ evalLeq h v
evalV h v@(VPlusLeqR {})   = VLeq $ evalLeq h v
evalV h v@(VComplLeq {})   = VLeq $ evalLeq h v
evalV h v@(VPlusSimple {}) = VPlus $ evalPlus h v
evalV h v@(VPlusLiftL {})  = VPlus $ evalPlus h v
evalV h v@(VPlusLiftR {})  = VPlus $ evalPlus h v
evalV h v@(VPlusComplL {}) = VPlus $ evalPlus h v
evalV h v@(VPlusComplR {}) = VPlus $ evalPlus h v
evalV h (VFold n)          = VVFold n
evalV h (VFoldMap v)       = evalV h v
evalV h v                  = VEq

evalLeq :: Env -> Evid -> EList
evalLeq h@(hp, _) (VVar i)  = is where
  VLeq is = hp !! i
evalLeq _ VLeqRefl          = Excl []
evalLeq h (VLeqTrans q1 q2) =
  case (evalLeq h q1, evalLeq h q2) of
    (Incl is, Incl js)    -> Incl (map (js !!) is)
    (Incl is, es@Excl {}) -> Incl (map (included es !!) is)
    (Excl ds, Incl js)    -> Incl [j | (i, j) <- zip [0..] js, i `notElem` ds]
    (Excl ds, Excl es)    -> Excl (go 0 0 ds es)
  where
    -- We need to compute the final list of excluded entries. An entry is
    -- excluded either because (a) it is excluded in `es`, or (b) from those
    -- left after `es`, it is excluded by `ds`. `n` counts the positions in the
    -- original record; `m` counts positions after the `es` are excluded.
    go :: Int -> Int -> [Int] -> [Int] -> [Int]
    go m n [] []       = []
    go m n ds (e : es)
      | n == e         = n : go m (n + 1) ds es
    go m n (d : ds) es
      | m == d         = n : go (m + 1) (n + 1) ds es
    go m n ds es       = go (m + 1) (n + 1) ds es
evalLeq _ (VLeqSimple is)   = Incl is
evalLeq h (VLeqLiftL _ q)   = evalLeq h q
evalLeq h (VLeqLiftR q _)   = evalLeq h q
evalLeq h (VPlusLeqL q)     = evalPlus h q
evalLeq h (VPlusLeqR q)     = dual (evalPlus h q)
evalLeq h (VComplLeq q)     = dual (evalLeq h q)
evalLeq _ q                 = error $ "bad evidence for evalLeq: " ++ show q

evalPlus :: Env -> Evid -> EList
evalPlus (hp, _) (VVar i)   = es
  where VPlus es = hp !! i
evalPlus _ (VPlusSimple es) = Incl [i | (i, Left _) <- zip [0..] es]
evalPlus h (VPlusLiftL _ q) = evalPlus h q
evalPlus h (VPlusLiftR q _) = evalPlus h q
evalPlus h (VPlusComplL q)  = dual (evalLeq h q)
evalPlus h (VPlusComplR q)  = evalLeq h q
evalPlus _ q                = error $ "bad evidence for evalPlus: " ++ show q
