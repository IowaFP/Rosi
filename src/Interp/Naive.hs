{-# LANGUAGE OverloadedStrings #-}
module Interp.Naive where

import Control.Monad.Reader (runReaderT)
import Data.IORef
import qualified Prettyprinter as P
import System.IO.Unsafe (unsafePerformIO)
import Printer
import Syntax

import GHC.Stack

import qualified Debug.Trace as T
{-# NOINLINE traceEvaluation #-}

traceEvaluation :: IORef Bool
traceEvaluation = unsafePerformIO (newIORef False)

trace s x =
  if unsafePerformIO (readIORef traceEvaluation)
  then T.trace s x
  else x

newtype Env = E ([Ty], [Value])
  deriving Show
data Value = VTyLam Env String Kind Term | VPrLam Env Pred Term | VLam Env String Ty Term | VIn Value
           | VSing Ty | VLabeled String Value
           | VRecord [(String, Value)] | VBranch [String] Value Value
           | VAna Ty Value | VSyn Ty Value

instance Show Value where
  show (VTyLam {}) = "VTyLam"
  show (VPrLam {}) = "VPrLam"
  show (VLam {}) = "VLam"
  show (VIn {}) = "VIn"
  show (VSing t) = "VSing"
  show (VLabeled s v) = "VLabeled"
  show (VRecord {}) = "VRecord"
  show (VBranch {}) = "VBranch"
  show (VAna _ e) = "VAna (" ++ show e ++ ")"
  show (VSyn _ e) = "VSyn (" ++ show e ++ ")"

-- prededence:
-- lambda   0
-- ?        1
-- in       2
instance Printable Value where
  ppr (VTyLam _ x k m) = with 0 $ ppr (ETyLam x (Just k) m)
  ppr (VPrLam _ p m) = with 0 $ ppr (EPrLam p m)
  ppr (VLam _ x t m) = ppr (ELam x (Just t) m)
  ppr (VIn v) = "in" <+> at 3 (ppr v)
  ppr (VLabeled s v) = fillSep [ppre s <+> ":=", ppr v]
  ppr (VRecord ps) = hang 2 $ parens $ fillSep $ punctuate "," [fillSep [ppre s <+> ":=", ppr m] | (s, m) <- ps]
  ppr (VBranch _ m n) = fillSep [at 2 (ppr m), "|" <+> ppr n]
  ppr (VAna f m) = "ana" <+> brackets (ppr f) <+> parens (ppr m)
  ppr (VSyn f m) = "syn" <+> brackets (ppr f) <+> parens (ppr m)

pprBinding :: String -> Value -> RDoc ann
pprBinding s v = hang 2 (fillSep [ppre s <+> "=", ppr v])

inst :: Env -> Value -> Inst -> Value
inst h v (PrArg _) = v
inst h v (TyArg t) = tyapp h v t

shiftE :: [Ty] -> [Ty]
shiftE = map (shiftT 0)

tyapp :: Env -> Value -> Ty -> Value
tyapp h (VTyLam (E (ht, he)) x _ f') t = eval (E (substTy h t : shiftE ht, he)) f'

app :: HasCallStack => Env -> Value -> Value -> Value
app _ (VLam (E (ht, he)) x _ f') v = eval (E (ht, v : he)) f'
app h (VBranch xs f' g') (VLabeled k v') = if k `elem` xs then appV h f' k v' else appV h g' k v'
app _ (VBranch xs f' g') v = error $ "evaluation failed: (" ++ show (VBranch xs f' g') ++ ") (" ++ show v ++ ")"
app h (VAna _ m) (VLabeled k v') = app h (app h (tyapp h (tyapp h m (TLab k)) (TPi (TRow []))) (VSing (TLab k))) v'
-- app _ (VTyLam h _ _ f) v = app h (eval h f) v
app _ (VPrLam h _ f) v = app h (eval h f) v
app _ f e = error $ "app failed (" ++ show f ++ ") (" ++ show e ++")"

appV :: Env -> Value -> String -> Value -> Value
appV _ (VLam (E (ht, he)) x _ f) k e' = eval (E (ht, VLabeled k e' : he)) f
appV h (VBranch xs f' g') k v' = if k `elem` xs then appV h f' k v' else appV h g' k v'
appV h (VAna _ m) k v' = app h (app h (tyapp h (tyapp h m (TLab k)) (TPi (TRow []))) (VSing (TLab k))) v'

eval :: HasCallStack => Env -> Term -> Value
eval h@(E (ht, _)) e = trace ("Eval: " ++ show e ++ " in " ++ show ht) $
           eval' h e

eval' :: HasCallStack => Env -> Term -> Value
eval' (E (_, he)) (EVar i x) =
  trace ("Environment: " ++ show he) $
  let result = he !! i in
  trace ("Variable " ++ show x ++ " is " ++ show result) $
  he !! i
eval' h (ELam s (Just t) e) = VLam h s t e
eval' h e0@(EApp (EInst (EConst CPrj) (Known [TyArg y, TyArg z, _])) e)   -- remember: y <= z
  | null ls = VRecord []
  | otherwise = prj (eval h e) where
    ls = dom e0 (substTy h y)
    prj (VRecord fs) = VRecord [(l, th) | (l, th) <- fs, l `elem` ls]
    prj v@VLabeled{} = v  -- can do dumb projections
    prj v@VSyn{} = v   -- synthesizing fewer fields is the same as synthesizing more fields
    -- alternatively, we could do the computation here:
    -- prj (VSyn _ m) = VRecord [(l, app (eval h m) (VSing (TLab l))) | l <- ls]
eval' h e@(EApp (EInst (EApp (EInst (EConst CConcat) (Known [TyArg x, TyArg y, _, _])) m) (Known [])) n) =
  VRecord (fields xls (eval h m) ++ fields yls (eval h n)) where
  xls = dom e (substTy h x)
  yls = dom e (substTy h y)
  fields _ (VRecord fs) = fs
  fields _ (VLabeled s th) = [(s, th)]
  fields ls (VSyn _ m) = [(l, app h m (VSing (TLab l))) | l <- ls]
  fields _ _ = error $ "evaluation failed: " ++ show e
eval' h (EApp (EInst (EConst CInj) (Known [TyArg y, TyArg z, _])) e) = eval h e
eval' h e@(EApp (EInst (EApp (EInst (EConst CBranch) (Known [TyArg x, TyArg y, _, _, _])) f) (Known [])) g) = VBranch (dom e (substTy h x)) (eval h f) (eval h g)
eval' h (EApp (EInst (EConst CIn) _) e) = VIn (eval h e) -- also treating in like a constructor... probably will need that functor evidence eventually, but meh
eval' h (EApp (EInst (EConst COut) _) e)
  | VIn v <- eval h e = v
eval' h e@(EApp (EInst (EConst CFix) is) f) = eval h (EApp f e)
eval' h (EApp f e) = app h (eval h f) (eval h e) where
  -- So yeah, supposed to be call-by-name here... relying on Haskell's laziness to delay evaluation
eval' h (ETyLam s (Just k) e) = VTyLam h s k e
eval' h (EInst e (Known is)) = foldl (inst h) (eval h e) is
eval' h e0@(EInst e (Unknown {})) = error $ "unexpected unknown instantiation: " ++ show e0
eval' h (ECast e _) = eval h e
eval' h (EPrLam _ e) = eval h e
eval' h (ESing t) = VSing (substTy h t)
eval' h (ELabel l e)
  | VSing (TLab s) <- eval h l = VLabeled s (eval h e)
eval' h@(E (_, he)) (EUnlabel e l) = unlabel (eval h e) where
  unlabel (VLabeled _ v) = v  -- ignoring the label entirely here...
  unlabel (VRecord [(_, v)]) = v
  unlabel e@(VSyn _ m)
    | VSing (TLab s) <- eval h l =
      let result = app h (tyapp h (tyapp h m (TLab s)) (TPi (TRow []))) (eval h l)  -- the label we're trying to remove is exactly the case we need to synthesize
      in
      trace ("Unlabeling " ++ show e) $
      trace ("Environment: " ++ show he) $
      trace ("Computed " ++ show result) $
      result

  unlabel v = error $ "Wut " ++ show v
eval' h (EAna f m) = VAna f (eval h m)
eval' h (ESyn f m) = VSyn f (eval h m)
eval' _ e = error $ "evaluation failed: " ++ show e

substTy :: Env -> Ty -> Ty
substTy h@(E (ht, _)) t = trace (unwords ["substTy:", show t, "->", show t', "in", show (length ht)]) t' where
  t' = substTy' h t


-- Other than being pure, why am I not using normalization here??...
substTy' :: Env -> Ty -> Ty
substTy' (E (ht, _)) t@(TVar i _)
  | i >= length ht = error $ "variable " ++ show t ++ " not in environment " ++ show ht
  | otherwise = ht !! i
substTy' h TUnif{} = error "substTy: TUnif"
substTy' h (TThen p t) = TThen p (substTy' h t)
substTy' (E (ht, he)) (TForall x (Just k) t) = TForall x (Just k) (substTy' (E (TVar 0 x : map (shiftT 0) ht, he)) t)
substTy' (E (ht, he)) (TLam x (Just k) t) = TLam x (Just k) (substTy' (E (TVar 0 x : map (shiftT 0) ht, he)) t)
substTy' e@(E (ht, he)) (TApp t u)
  | TLam _ _ body <- t' = substTy' (E (u' : shiftE ht, he)) body
  | TMapFun f <- t', TRow lts <- u', Just ps <- mapM splitLabel lts = TRow [TLabeled l (substTy' e (TApp f t)) | (l, t) <- ps]
  | otherwise = TApp t' u'
  where t' = substTy' e t
        u' = substTy' e u
substTy' h t@TLab {} = t
substTy' h (TSing t) = TSing (substTy' h t)
substTy' h (TLabeled l t) = TLabeled (substTy' h l) (substTy' h t)
substTy' h (TRow fs) = TRow (map (substTy' h ) fs)
substTy' h (TPi t) = TPi (substTy' h t)
substTy' h (TSigma t) = TSigma (substTy' h t)
substTy' h (TMu t) = TMu (substTy' h t)
substTy' h TFun = TFun
substTy' h (TMapFun t) = TMapFun (substTy' h t)
substTy' h (TMapArg t) = TMapArg (substTy' h t)
substTy' h (TInst _ t) = substTy' h t
substTy' h (TCompl z y)
  | TRow zs <- substTy' h z, TRow ys <- substTy' h y, Just zps <- mapM splitLabel zs, Just yps <- mapM splitLabel ys =
      TRow [uncurry TLabeled zp | zp <- zps, fst zp `notElem` map fst yps]
substTy' h t = error $ "substTy missing cases: " ++ show t

dom :: HasCallStack => Term -> Ty -> [String]
dom e0 (TRow ts) = map labelFrom ts where
  labelFrom (TLabeled (TLab s) _) = s
  labelFrom t = error $ "no label: " ++ show (TRow ts) ++ " in " ++ show e0
dom e0 t = error $ "no domain: " ++ show t ++ " in " ++ show e0