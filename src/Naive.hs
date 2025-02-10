{-# LANGUAGE OverloadedStrings #-}
module Naive (module Naive) where

import Control.Monad.Reader (runReaderT)
import qualified Prettyprinter as P
import Printer
import Syntax

-- import Debug.Trace
trace _ x = x

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
  show (VSing {}) = "VSing"
  show (VLabeled {}) = "VLabeled"
  show (VRecord {}) = "VRecord"
  show (VBranch {}) = "VBranch"
  show (VAna _ e) = "VAna (" ++ show e ++ ")"
  show (VSyn _ e) = "VSyn (" ++ show e ++ ")"


-- prededence:
-- lambda   0
-- ?        1
-- in       2
instance Printable Value where
  ppr (VTyLam _ x k m) = with 0 $ ppr (ETyLam x k m)
  ppr (VPrLam _ p m) = with 0 $ ppr (EPrLam p m)
  ppr (VLam _ x t m) = ppr (ELam x t m)
  ppr (VIn v) = "in" <+> at 3 (ppr v)
  ppr (VLabeled s v) = fillSep [ppre s <+> ":=", ppr v]
  ppr (VRecord ps) = hang 2 $ parens $ fillSep $ punctuate "," [fillSep [ppre s <+> ":=", ppr m] | (s, m) <- ps]
  ppr (VBranch _ m n) = fillSep [at 2 (ppr m), "?" <+> ppr n]
  ppr (VAna f m) = "ana" <+> brackets (ppr f) <+> parens (ppr m)
  ppr (VSyn f m) = "syn" <+> brackets (ppr f) <+> parens (ppr m)

pprBinding :: String -> Value -> RDoc ann
pprBinding s v = hang 2 (fillSep [ppre s <+> "=", ppr v])

inst :: Env -> Value -> Inst -> Value
inst h v (PrArg _) = v
inst h v (TyArg t) = tyapp h v t

tyapp :: Env -> Value -> Ty -> Value
tyapp h (VTyLam (E (ht, he)) x _ f') t = eval (E (substTy h t : map (shiftT 0) ht, he)) f'

app :: Env -> Value -> Value -> Value
app _ (VLam (E (ht, he)) x _ f') v = eval (E (ht, v : he)) f'
app h (VBranch xs f' g') (VLabeled k v') = if k `elem` xs then appV h f' k v' else appV h g' k v'
app _ (VBranch xs f' g') v = error $ "evaluation failed: (" ++ show (VBranch xs f' g') ++ ") (" ++ show v ++ ")"
app h (VAna _ m) (VLabeled k v') = app h (app h (tyapp h m (TLab k)) (VSing (TLab k))) v'
app _ (VTyLam h _ _ f) v = app h (eval h f) v
app _ (VPrLam h _ f) v = app h (eval h f) v
app _ f e = error $ "app failed (" ++ show f ++ ") (" ++ show e ++")"

appV :: Env -> Value -> String -> Value -> Value
appV _ (VLam (E (ht, he)) x _ f) k e' = eval (E (ht, VLabeled k e' : he)) f
appV h (VBranch xs f' g') k v' = if k `elem` xs then appV h f' k v' else appV h g' k v'
appV h (VAna _ m) k v' = app h (app h (tyapp h m (TLab k)) (VSing (TLab k))) v'

eval :: Env -> Term -> Value
eval h e = trace ("Eval: " ++ show e) (eval' h e)

eval' (E (_, he)) (EVar i x) =
  trace ("Environment: " ++ show he) $
  let result = he !! i in
  trace ("Variable " ++ show x ++ " is " ++ show result) $
  he !! i
eval' h (ELam s t e) = VLam h s t e
eval' h (EApp (EInst (EConst CPrj) (Known [TyArg y, TyArg z, _])) e)   -- remember: y <= z
  | null ls = VRecord []
  | otherwise = prj (eval h e) where
    ls = dom y
    prj (VRecord fs) = VRecord [(l, th) | (l, th) <- fs, l `elem` ls]
    prj v@VLabeled{} = v  -- can do dumb projections
    prj v@VSyn{} = v   -- synthesizing fewer fields is the same as synthesizing more fields
    -- alternatively, we could do the computation here:
    -- prj (VSyn _ m) = VRecord [(l, app (eval h m) (VSing (TLab l))) | l <- ls]
eval' h e@(EApp (EInst (EApp (EInst (EConst CConcat) (Known [TyArg x, TyArg y, _, _])) m) (Known [])) n) =
  VRecord (fields xls (eval h m) ++ fields yls (eval h n)) where
  xls = dom x
  yls = dom y
  fields _ (VRecord fs) = fs
  fields _ (VLabeled s th) = [(s, th)]
  fields ls (VSyn _ m) = [(l, app h m (VSing (TLab l))) | l <- ls]
  fields _ _ = error $ "evaluation failed: " ++ show e
eval' h (EApp (EInst (EConst CInj) (Known [TyArg y, TyArg z, _])) e) = eval h e
eval' h (EApp (EInst (EApp (EInst (EConst CBranch) (Known [TyArg x, TyArg y, _, _, _])) f) (Known [])) g) = VBranch (dom x) (eval h f) (eval h g)
eval' h (EApp (EInst (EConst CIn) _) e) = VIn (eval h e) -- also treating in like a constructor... probably will need that functor evidence eventually, but meh
eval' h (EApp (EInst (EConst COut) _) e)
  | VIn v <- eval h e = v
-- eval' h@(E (ht, he)) (EFix x t e) = eval (E (ht, eval h e : he)) e
eval' h (EApp f e) = app h (eval h f) (eval h e) where
  -- So yeah, supposed to be call-by-name here... relying on Haskell's laziness to delay evaluation
eval' h (ETyLam s k e) = VTyLam h s k e
eval' h (EInst e (Known is)) = foldl (inst h) (eval h e) is
eval' h e0@(EInst e (Unknown g)) = error $ "unexpected unknown instantiation: " ++ show e0
eval' h (ETyEqu e _) = eval h e
eval' h (EPrLam _ e) = eval h e
eval' h (ESing t) = VSing (substTy h t)
eval' h (ELabel l e)
  | VSing (TLab s) <- eval h l = VLabeled s (eval h e)
eval' h@(E (_, he)) (EUnlabel e l) = unlabel (eval h e) where
  unlabel (VLabeled _ v) = v  -- ignoring the label entirely here...
  unlabel (VRecord [(_, v)]) = v
  unlabel e@(VSyn _ m)
    | VSing (TLab s) <- eval h l =
      let result = app h (tyapp h m (TLab s)) (eval h l)  -- the label we're trying to remove is exactly the case we need to synthesize
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
substTy (E (ht, _)) t@(TVar i _ _) = ht !! i
substTy h TUnif{} = error "substTy: TUnif"
substTy h (TThen p t) = TThen p (substTy h t)
substTy (E (ht, he)) (TForall x k t) = TForall x k (substTy (E (TVar 0 x (Just k) : map (shiftT 0) ht, he)) t)
substTy (E (ht, he)) (TLam x k t) = TLam x k (substTy (E (TVar 0 x (Just k) : map (shiftT 0) ht, he)) t)
substTy h (TApp t u) = TApp (substTy h t) (substTy h u)
substTy h t@TLab {} = t
substTy h (TSing t) = TSing (substTy h t)
substTy h (TLabeled l t) = TLabeled (substTy h l) (substTy h t)
substTy h (TRow fs) = TRow (map (substTy h ) fs)
substTy h (TPi t) = TPi (substTy h t)
substTy h (TSigma t) = TSigma (substTy h t)
substTy h (TMu t) = TMu (substTy h t)
substTy h (TMapFun t) = TMapFun (substTy h t)
substTy h (TMapArg t) = TMapArg (substTy h t)

dom :: Ty -> [String]
dom (TRow ts) = map labelFrom ts where
  labelFrom (TLabeled (TLab s) _) = s
  labelFrom t = error $ "no label: " ++ show t
dom t = error $ "no domain: " ++ show t