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
  show (Term t) = renderString False (ppr t)
  show (Prim _) = "<<prim>>"

data Value = VPrLam Env Body | VLam Env Body
           | VIn Value | VSing | VVariant Int Value | VRecord [Value] | VSyn (Int -> Value)

instance Show Value where
  show (VPrLam _ b) = "\\p " ++ show b
  show (VLam _ b) = "\\ " ++ show b
  show (VIn v) = "in (" ++ show v ++ ")"
  show VSing = "()"
  show (VVariant k w) = "<" ++ show k ++ ", " ++ show w ++ ">"
  show (VRecord vs) = "(" ++ intercalate ", " (map show vs) ++ ")"
  show (VSyn t) = "<<syn>>"


data EValue = VLeq [Int] | VPlus [Either Int Int] | VEq
  deriving Show

evalB :: Env -> Body -> Value
evalB h (Term e) = eval h e
evalB h (Prim f) = f h

app :: Env -> Value -> Value -> Value
app _ (VLam (hp, he) f') v = evalB (hp, v : he) f'
app h v w = error $ "don't know how to apply " ++ show v ++ " to " ++ show w

prapp :: Env -> Value -> EValue -> Value
prapp _ f@(VPrLam (hp, he) f') v =
  evalB (v : hp, he) f'

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
eval h e = trace ("Eval: " ++ renderString False (ppr e)) $
           eval' h e

eval' (_, he) (EVar i _)
  | i < length he = he !! i
  | otherwise = error $ "environment too small for variable " ++ show i ++ ": " ++ show he
eval' h (ELam _ _ e) = VLam h (Term e)
eval' h (EApp f e) = app h (eval h f) (eval h e)
eval' h (ETyLam _ _ e) = eval h e
eval' h (EPrLam _ e) = VPrLam h (Term e)
eval' h (EInst t (Known is)) = inst (eval h t) is where
  inst v []             = v
  inst v (TyArg _ : is) = inst v is
  inst v (PrArg q : is) = inst (prapp h v (evalV h q)) is
eval' h (ESing _) = VSing
eval' h (ELabel l e) = eval h e
eval' h (EUnlabel e l) =
  case eval h e of
    VRecord [v] -> v
    VVariant 0 v -> v
    VSyn f -> f 0
    v -> v
eval' h (EConst CPrj) = -- VPrLam h (Value (VLam h (Const CPrj)))
  VPrLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
    case h of
      (VLeq is : _, v : _) ->
        case v of
          VSyn f -> VSyn (\i -> f (is !! i))
          _ -> VRecord (map (recordFrom v) is)
      _ -> error $ "bad environment for prj: " ++ show h
eval' h (EConst CInj) = -- VPrLam h (Value (VLam h (Const CPrj)))
  VPrLam h $ Prim $ \ h ->
  VLam h $ Prim $ \ h ->
    case h of
      (VLeq is : _, v : _) ->
        let (k, w) = variantFrom v in
        VVariant (is !! k) w
      _ -> error $ "bad environment for inj: " ++ show h
eval' h (EConst CConcat) = -- VPrLam h (Value (VLam h (Value (VLam h (Const CConcat)))))
  VPrLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \ (VPlus is : _, w : v : _) ->
    case (v, w) of
      (VSyn f, w) ->
        let ws = recordFrom w
            pick (Left i) = f i
            pick (Right i) = ws i in
        VSyn (\i -> pick (is !! i))
      (v, VSyn g) ->
        let vs = recordFrom v
            pick (Left i) = vs i
            pick (Right i) = g i in
        VSyn (\i -> pick (is !! i))
      _ ->
        let ws = recordFrom w
            vs = recordFrom v
            pick (Left i) = vs i
            pick (Right i) = ws i in
        VRecord [pick (is !! i) | i <- [0..recordSize v + recordSize w - 1]]
eval' h (EConst CBranch) = -- VPrLam h (Value (VLam h (Value (VLam h (Value (VLam h (Const CBranch)))))))
  VPrLam h $ Prim $ \h ->
  VLam h $ Prim $ \h ->
  VLam h $ Prim $ \ h ->
  VLam h $ Prim $ \h ->
    case h of
      (VPlus is : _, v : g : f : _) ->
        let (k, w) = variantFrom v in
        trace ("branch: constructor is " ++ show k ++
               " and evidence is " ++ show is ++ " so calling " ++
               (case is !! k of Left _ -> show f; Right _ -> show g)) $
        case is !! k of
          Left i  -> app h f (VVariant i w)
          Right i -> app h g (VVariant i w)
      _ -> error $ "bad environment for branch: " ++ show h
eval' h (EConst CIn) = -- VLam h (Const CIn)
  VLam h $ Prim $ \ (_, v : _) -> VIn v
eval' h (EConst COut) = -- VLam h (Const COut)
  VLam h $ Prim $ \ h ->
    case h of
      (_, VIn v : _) -> v
      _ -> error $ "bad environment for out: " ++ show h
eval' h (EConst CFix) = -- VLam h (Const CFix)
  eval h (ELam "f" Nothing (EApp (EVar 0 "f") (EApp (EConst CFix) (EVar 0 "f"))))
--   VLam h $ Prim $ \ (_, VLam (hp, he) (Term e) : _) ->
--     eval (hp, eval h (EApp (EConst CFix) (ELam "x" Nothing e)) : he) e
eval' h (ESyn _ e) = VSyn (\i -> app h (prapp h f (VLeq [i])) VSing)
  where f = eval h e
eval' h (EAna _ e) =
  VLam h $ Prim $ \ (_, VVariant k w : _) ->
    app h (app h (prapp h f (VLeq [k])) VSing) w
  where f = eval h e
eval' h (ECast e (VEqTyConSing Pi)) =
  case eval h e of
    VRecord [v] -> v
    VSyn f      -> f 0
eval' h (ECast e (VEqSym (VEqTyConSing Pi))) =
  VRecord [eval h e]
eval' h (ECast e (VEqTyConSing Sigma)) = v
  where VVariant 0 v = eval h e
eval' h (ECast e (VEqSym (VEqTyConSing Sigma))) =
  VVariant 0 (eval h e)
eval' h (ECast e q) = eval h e
eval' h (ETyped e _) = eval h e

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
evalV h v                  = VEq

evalLeq :: Env -> Evid -> [Int]
evalLeq h@(hp, _) = go False where

  go compl (VVar i) = go compl (VLeqSimple is) where
    VLeq is = hp !! i
  go False VLeqRefl = [0..]
  go True VLeqRefl = []
  go compl (VLeqTrans q1 q2)
    | compl = filter (`notElem` ks) [0..]
    | otherwise = ks
    where is = go False q1
          js = go False q2
          ks = map (js !!) is
  go False (VLeqSimple is) = is
  go True (VLeqSimple is) = filter (`notElem` is) [0..]
  go compl (VLeqLiftL _ q) = go compl q
  go compl (VLeqLiftR q _) = go compl q
  go compl (VPlusLeqL q) = map snd (sortOn fst [(i, j) | (j, Left i) <- zip [0..] es])
    where es = evalPlus h q
  go compl (VPlusLeqR q) = map snd (sortOn fst [(i, j) | (j, Right i) <- zip [0..] es])
    where es = evalPlus h q
  go compl (VComplLeq q) = go (not compl) q
  go compl v = error $ "bad evidence for leq: " ++ show v

evalPlus :: Env -> Evid -> [Either Int Int]
evalPlus h v = evalPlus' h v


evalPlus' (hp, _) (VVar i) = es
  where VPlus es = hp !! i
evalPlus' h (VPlusSimple es) = es
evalPlus' h (VPlusLiftL _ q) = evalPlus' h q
evalPlus' h (VPlusLiftR q _) = evalPlus' h q
evalPlus' h (VPlusComplL q) = map pick [0..]
  where is = evalLeq h q
        pick i = case elemIndex i is of
                   Just j -> Right j
                   Nothing -> Left (i - length [j | j <- is, j < i])
evalPlus' h (VPlusComplR q) = map pick [0..]
  where is = evalLeq h q
        pick i = case elemIndex i is of
                   Just j -> Left j
                   Nothing -> Right (i - length [j | j <- is, j < i])
evalPlus' _ v = error $ "bad evidence for plus: " ++ show v