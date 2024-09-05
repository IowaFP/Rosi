{-# LANGUAGE OverloadedStrings #-}
module Naive where

import Control.Monad.Reader (runReaderT)
import qualified Data.Map as M
import qualified Prettyprinter as P
import Printer

import Syntax 

newtype Env = E (M.Map String Ty, M.Map String Value)
  deriving Show
data Value = VTyLam Env String Kind Term | VPrLam Env String Pred Term | VLam Env String Ty Term | VIn Value
           | VSing Ty | VLabeled String Value
           | VRecord [(String, Value)] | VBranch [String] Value Value
           | VAna Ty Term | VSyn Ty Term 

instance Show Value where
  show (VTyLam {}) = "VTyLam"
  show (VPrLam {}) = "VPrLam"
  show (VLam {}) = "VLam"
  show (VIn {}) = "VIn"
  show (VSing {}) = "VSing"
  show (VLabeled {}) = "VLabeled"
  show (VRecord {}) = "VRecord"
  show (VBranch {}) = "VBranch"
  show (VAna {}) = "VAna"
  show (VSyn {}) = "VSyn"


-- prededence:
-- lambda   0
-- ?        1
-- in       2
instance Printable Value where
  ppr (VTyLam _ x k m) = with 0 $ ppr (ETyLam x k m)
  ppr (VPrLam _ x p m) = with 0 $ ppr (EPrLam x p m)
  ppr (VLam _ x t m) = ppr (ELam x t m)
  ppr (VIn v) = "in" <+> at 3 (ppr v)
  ppr (VLabeled s v) = fillSep [ppre s <+> ":=", ppr v]
  ppr (VRecord ps) = hang 2 $ parens $ fillSep $ punctuate "," [fillSep [ppre s <+> ":=", ppr m] | (s, m) <- ps]
  ppr (VBranch _ m n) = fillSep [at 2 (ppr m), "?" <+> ppr n]
  ppr (VAna f m) = ppr (EAna f m)
  ppr (VSyn f m) = ppr (ESyn f m)

pprBinding :: String -> Value -> RDoc ann
pprBinding s v = hang 2 (fillSep [ppre s <+> "=", ppr v])  

tyapp :: Env -> Value -> Ty -> Value
tyapp h (VTyLam (E (ht, he)) x _ f') t = eval (E (M.insert x (substTy h t) ht, he)) f'

app :: Env -> Value -> Value -> Value
app _ (VLam (E (ht, he)) x _ f') v = eval (E (ht, M.insert x v he)) f'
app h (VBranch xs f' g') (VLabeled k v') = if k `elem` xs then appV h f' k v' else appV h g' k v'
app _ (VBranch xs f' g') v = error $ "evaluation failed: (" ++ show (VBranch xs f' g') ++ ") (" ++ show v ++ ")"
app h (VAna _ m) (VLabeled k v') = app h (app h (tyapp h (eval h m) (TLab k)) (VSing (TLab k))) v'
app _ (VTyLam h _ _ f) v = app h (eval h f) v
app _ (VPrLam h _ _ f) v = app h (eval h f) v
app _ f e = error $ "app failed (" ++ show f ++ ") (" ++ show e ++")"
  
appV :: Env -> Value -> String -> Value -> Value
appV _ (VLam (E (ht, he)) x _ f) k e' = eval (E (ht, M.insert x (VLabeled k e') he)) f
appV h (VBranch xs f' g') k v' = if k `elem` xs then appV h f' k v' else appV h g' k v'
appV h (VAna _ m) k v' = app h (app h (tyapp h (eval h m) (TLab k)) (VSing (TLab k))) v'

eval :: Env -> Term -> Value
eval (E (_, he)) (EVar x)
  | Just v <- M.lookup x he = v
eval h (ELam s t e) = VLam h s t e
eval h (EApp f e) = app h (eval h f) (eval h e) where
  -- So yeah, supposed to be call-by-name here... relying on Haskell's laziness to delay evaluation

eval h (ETyLam s k e) = VTyLam h s k e
eval h (ETyApp f t) = tyapp h (eval h f) t
eval h (ETyEqu e _) = eval h e  
eval h (EPrLam _ _ e) = eval h e
eval h (EPrApp e _) = eval h e
eval h (ESing t) = VSing (substTy h t)
eval h (ELabeled l e) 
  | VSing (TLab s) <- eval h l = VLabeled s (eval h e)
eval h (EUnlabel e l) = unlabel (eval h e) where
  unlabel (VLabeled _ v) = v  -- ignoring the label entirely here...
  unlabel (VRecord [(_, v)]) = v
  unlabel (VSyn _ m) 
    | VSing (TLab s) <- eval h l = app h (tyapp h (eval h m) (TLab s)) (eval h l)  -- the label we're trying to remove is exactly the case we need to synthesize
  unlabel v = error $ "Wut " ++ show v
eval h (EPrj y z _ e)   -- remember: y <= z
  | null ls = VRecord []
  | otherwise = prj (eval h e) where
    ls = dom y
    prj (VRecord fs) = VRecord [(l, th) | (l, th) <- fs, l `elem` ls]
    prj v@VLabeled{} = v  -- can do dumb projections      
    prj v@VSyn{} = v   -- synthesizing fewer fields is the same as synthesizing more fields
    -- alternatively, we could do the computation here:
    -- prj (VSyn _ m) = VRecord [(l, app (eval h m) (VSing (TLab l))) | l <- ls] 
eval h e@(EConcat x y _ _ m n) = VRecord (fields xls (eval h m) ++ fields yls (eval h n)) where
  xls = dom x
  yls = dom y
  fields _ (VRecord fs) = fs
  fields _ (VLabeled s th) = [(s, th)]
  fields ls (VSyn _ m) = [(l, app h (eval h m) (VSing (TLab l))) | l <- ls] 
  fields _ _ = error $ "evaluation failed: " ++ show e
eval h (EInj _ _ _ e) = eval h e
eval h (EBranch x y z _ f g) = VBranch (dom x) (eval h f) (eval h g)
eval h (EAna f m) = VAna f m
eval h (ESyn f m) = VSyn f m 
eval h (EIn _ e) = VIn (eval h e) -- also treating in like a constructor... probably will need that functor evidence eventually, but meh
eval h (EOut e) 
  | VIn v <- eval h e = v
eval h@(E (ht, he)) (EFix x t e) = eval (E (ht, M.insert x (eval h e) he)) e
eval _ e = error $ "evaluation failed: " ++ show e

substTy :: Env -> Ty -> Ty
substTy (E (ht, _)) t@(TVar x _)
  | Just t' <- M.lookup x ht = t'
  | otherwise = t
substTy h TUnif{} = error "substTy: TUnif"  
substTy h (TThen p t) = TThen p (substTy h t) 
substTy (E (ht, he)) (TForall x k t) = TForall x k (substTy (E (M.delete x ht, he)) t)
substTy (E (ht, he)) (TLam x k t) = TLam x k (substTy (E (M.delete x ht, he)) t)
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