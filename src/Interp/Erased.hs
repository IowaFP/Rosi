module Interp.Erased where

import Control.Monad.Reader
import Data.IORef
import Data.List (elemIndex, intercalate, sortOn)
import Printer
import Syntax

import qualified Debug.Trace as T
import GHC.Stack
import System.IO.Unsafe

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

data Value = VPrLam Env Body | VLam Env Body
           | VSing | VVariant Int Value | VRecord [Value] | VSyn (Int -> Value)
           | VString String

instance Show Value where
  show (VPrLam _ b) = "\\p " ++ show b
  show (VLam _ b) = "\\ " ++ show b
  show VSing = "()"
  show (VVariant k w) = "<" ++ show k ++ ", " ++ show w ++ ">"
  show (VRecord vs) = "(" ++ intercalate ", " (map show vs) ++ ")"
  show (VSyn t) = "<<syn>>"
  show (VString s) = "\"" ++ s ++ "\""

data EList t = Bounded [t] | Unbounded [t]
  deriving (Show, Foldable, Functor, Traversable)

(<!>) :: EList t -> Int -> t
Bounded xs <!> n = xs !! n
Unbounded xs <!> n = xs !! n

listFrom :: EList t -> (Bool, [t])
listFrom (Bounded xs) = (True,  xs)
listFrom (Unbounded xs) = (False, xs)

data EValue = VLeq (EList Int) | VPlus (EList (Either Int Int)) | VEq | VVFold Int
  deriving Show

evalB :: Env -> Body -> Value
evalB h (Term e) = eval h e
evalB h (Prim f) = f h

app :: Value -> Value -> Value
app (VLam (hp, he) f') v = evalB (hp, v : he) f'
app v w = error $ "don't know how to apply " ++ show v ++ " to " ++ show w

prapp :: Value -> EValue -> Value
prapp f@(VPrLam (hp, he) f') v =
  evalB (v : hp, he) f'
prapp f v =
  error $ "don't know how to apply " ++ show f ++ " to " ++ show v

recordFrom :: HasCallStack => Value -> Int -> Value
recordFrom (VRecord vs) i = vs !! i
recordFrom (VSyn f) i     = f i
recordFrom v _            = v

recordSize :: HasCallStack => Value -> Int
recordSize (VRecord vs) = length vs
recordSize (VSyn f)     = error "unbounded"
recordSize v            = 1

variantFrom :: HasCallStack => Value -> (Int, Value)
variantFrom (VVariant k v) = (k, v)
variantFrom v              = (0, v)

eval, eval' :: HasCallStack => Env -> Term -> Value
eval h e = -- trace ("Eval: " ++ renderString (ppr e)) $
           eval' h e

eval' (_, he) (EVar i _)
  | i < length he = he !! i
  | otherwise = error $ "environment too small for variable " ++ show i ++ ": " ++ show he
eval' h (ELam _ _ e) = VLam h (Term e)
eval' h (EApp f e) = app (eval h f) (eval h e)
eval' h (ELet x e f) = eval h (EApp (ELam x Nothing f) e)
eval' h (ETyLam _ _ e) = eval h e
eval' h (EPrLam _ e) = VPrLam h (Term e)
eval' h (EInst t (Known is)) = inst (eval h t) is where
  inst v []             = v
  inst v (TyArg _ : is) = inst v is
  inst v (PrArg q : is) = inst (prapp v (evalV h q)) is
eval' h (ESing _) = VSing
eval' h (ELabel (Just k) l e) =
  case k of
    Pi -> VRecord [v]
    Sigma -> VVariant 0 v
  where v = eval h e
eval' h e0@(EUnlabel (Just k) e l) = -- eval h e
  case (k, v) of
    (Sigma, VVariant _ v) -> v
    (Pi, VRecord [v]) -> v
    (Pi, VSyn f) -> f 0
  where v = eval h e
eval' h (EConst CPrj) = -- VPrLam h (Value (VLam h (Const CPrj)))
  VPrLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
    case h of
      (VLeq (Bounded is) : _, VSyn f : _) ->
        VRecord (map f is)
      (VLeq (Unbounded is) : _, VSyn f : _) ->
        VSyn (\i -> f (is !! i))
      (VLeq (Bounded is) : _, VRecord vs : _) ->
        VRecord (map (vs !!) is)
      (VLeq (Unbounded is) : _, VRecord vs : _) ->
        VRecord [vs !! j | j <- takeWhile (< length vs) is]
      _ -> error $ "bad environment for prj: " ++ show h
eval' h (EConst CInj) = -- VPrLam h (Value (VLam h (Const CPrj)))
  VPrLam h $ Prim $ \ h ->
  VLam h $ Prim $ \ h ->
    case h of
      (VLeq is : _, v : _) ->
        let (k, w) = variantFrom v in
        VVariant (is <!> k) w
      _ -> error $ "bad environment for inj: " ++ show h
eval' h (EConst CConcat) = -- VPrLam h (Value (VLam h (Value (VLam h (Const CConcat)))))
  VPrLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \case
    (VPlus (Bounded is) : _, w : v : _) ->
      let ws = recordFrom w
          vs = recordFrom v
          pick (Left i) = vs i
          pick (Right j) = ws j in
      VRecord [pick i | i <- is]
    (VPlus (Unbounded is) : _, VRecord ws : VRecord vs : _) ->
      let pick (Left i) = vs !! i
          pick (Right i) = ws !! i in
      VRecord [pick (is !! i) | i <- [0..length vs + length ws - 1]]
    (VPlus (Unbounded is) : _, w : v : _) ->
      let vs = recordFrom v
          ws = recordFrom w
          pick (Left i) = vs i
          pick (Right i) = ws i in
      VSyn (\i -> pick (is !! i))
eval' h (EConst CBranch) = -- VPrLam h (Value (VLam h (Value (VLam h (Value (VLam h (Const CBranch)))))))
  VPrLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \case
    (VPlus is : _, v : g : f : _) ->
      let (k, w) = variantFrom v in
      trace ("branch: constructor is " ++ show k ++
              " and evidence is " ++ show is ++ " so calling " ++
              (case is <!> k of Left _ -> show f; Right _ -> show g)) $
      case is <!> k of
        Left i  -> app f (VVariant i w)
        Right i -> app g (VVariant i w)
    _ -> error $ "bad environment for branch: " ++ show h
eval' h (EConst CFix) = -- VLam h (Const CFix)
  eval h (ELam "f" Nothing (EApp (EVar 0 ["f", ""]) (EApp (EConst CFix) (EVar 0 ["f", []]))))
eval' h (EConst CStringCat) =
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \case
    (_, VString s1 : VString s0 : _) ->
       VString (s0 ++ s1)
    _ -> error $ "bad environment for (^): " ++ show h
eval' h (EConst CSyn) =
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \case
    (_, f : _) ->
      VSyn (\i -> app (prapp f (VLeq (Bounded [i]))) VSing)
eval' h (EConst CAna) =
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \case
    (_, VVariant k w : f : _) ->
      app (app (prapp f (VLeq (Bounded [k]))) VSing) w
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
          one k = app (app (prapp single (VLeq $ Bounded [k])) VSing) (vs k)
      in if n == 0 then def else foldl (\v w -> app (app comp v) w) (one 0) (map one [1..n - 1])
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

evalLeq :: Env -> Evid -> EList Int
evalLeq h@(hp, _) = go False where

  go :: Bool -> Evid -> EList Int
  go False (VVar i) = is where
    VLeq is = hp !! i
  go True (VVar i) = Unbounded $ filter (`notElem` is) [0..] where
    VLeq is = hp !! i
  go False VLeqRefl = Unbounded [0..]
  go True VLeqRefl = Bounded []
  go compl (VLeqTrans q1 q2)
    | compl = Unbounded $ filter (`notElem` ks) [0..]
    | otherwise = ks
    where is = go False q1
          js = go False q2
          ks = fmap (js <!>) is
  go False (VLeqSimple is) = Bounded is
  go True (VLeqSimple is) = Unbounded $ filter (`notElem` is) [0..]
  go compl (VLeqLiftL _ q) = go compl q
  go compl (VLeqLiftR q _) = go compl q
  go compl (VPlusLeqL q) = k $ map snd (sortOn fst [(i, j) | (j, Left i) <- zip [0..] es])
    where (esBounded, es) = listFrom $ evalPlus h q
          k | esBounded = Bounded
            | otherwise = Unbounded
  go compl (VPlusLeqR q) = k $ map snd (sortOn fst [(i, j) | (j, Right i) <- zip [0..] es])
    where (esBounded, es) = listFrom $ evalPlus h q
          k | esBounded = Bounded
            | otherwise = Unbounded
  go compl (VComplLeq q) = go (not compl) q
  go compl v = error $ "bad evidence for leq: " ++ show v

evalPlus :: Env -> Evid -> EList (Either Int Int)
evalPlus h v = evalPlus' h v

evalPlus' :: Env -> Evid -> EList (Either Int Int)
evalPlus' (hp, _) (VVar i) = es
  where VPlus es = hp !! i
evalPlus' h (VPlusSimple es) = Bounded $ es
evalPlus' h (VPlusLiftL _ q) = evalPlus' h q
evalPlus' h (VPlusLiftR q _) = evalPlus' h q
evalPlus' h (VPlusComplL q) = Unbounded $ map pick [0..]
  where is = evalLeq h q
        pick i = case elemIndex i (snd $ listFrom is) of
                   Just j -> Right j
                   Nothing -> Left (i - length [j | j <- snd (listFrom is), j < i])
evalPlus' h (VPlusComplR q) = Unbounded $ map pick [0..]
  where is = evalLeq h q
        pick i = case elemIndex i (snd $ listFrom is) of
                   Just j -> Left j
                   Nothing -> Right (i - length [j | j <- snd (listFrom is), j < i])
evalPlus' _ v = error $ "bad evidence for plus: " ++ show v