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

shiftE :: Int -> Term -> Term
shiftE j (EVar i x) 
  | i >= j = EVar (i + 1) x
  | otherwise = EVar i x
shiftE j (ELam x t m) = ELam x t (shiftE (j + 1) m)
shiftE j (EApp m n) = EApp (shiftE j m) (shiftE j n)
shiftE j (ETyLam x k m) = ETyLam x k (shiftE j m)
shiftE j (ETyApp m t) = ETyApp (shiftE j m) t
shiftE j m@(ESing {}) = m
shiftE j (ELabel l m) = ELabel (shiftE j l) (shiftE j m)
shiftE j (EUnlabel m l) = EUnlabel (shiftE j m) (shiftE j l)
shiftE j (EPrj y z d m) = EPrj y z d (shiftE j m)
shiftE j (EConcat x y z d m n) = EConcat x y z d (shiftE j m) (shiftE j n)
shiftE j (EInj y z d m) = EInj y z d (shiftE j m)
shiftE j (EBranch x y z d m n) = EBranch x y z d (shiftE j m) (shiftE j n)
shiftE j (ESyn t m) = ESyn t (shiftE j m)
shiftE j (EAna t m) = EAna t (shiftE j m)
shiftE j (EFold m1 m2 m3 n) = EFold (shiftE j m1) (shiftE j m2) (shiftE j m3) (shiftE j n)
shiftE j (EIn m n) = EIn (shiftE j m) (shiftE j n)
shiftE j (EOut m) = EOut (shiftE j m)
shiftE j (EFix x t m) = EFix x t (shiftE j m)
shiftE j (EPrLam p m) = EPrLam p (shiftE j m)
shiftE j (EPrApp m d) = EPrApp (shiftE j m) d
shiftE j (ETyEqu m q) = ETyEqu (shiftE j m) q

shiftV :: Int -> Value -> Value
shiftV j (VTyLam h x k m) = VTyLam (shiftH j h) x k (shiftE j m)
shiftV j (VPrLam h p m) = VPrLam (shiftH j h) p (shiftE j m)
shiftV j (VLam h x t m) = VLam (shiftH j h) x t (shiftE j m)
shiftV j (VIn v) = VIn (shiftV j v)
shiftV j (VSing t) = VSing t
shiftV j (VLabeled l v) = VLabeled l (shiftV j v)
shiftV j (VRecord fs) = VRecord [(l, shiftV j v) | (l, v) <- fs]
shiftV j (VBranch ls v w) = VBranch ls (shiftV j v) (shiftV j w)
shiftV j (VAna t m) = VAna t (shiftV j m)
shiftV j (VSyn t m) = VSyn t (shiftV j m)


shiftH :: Int -> Env -> Env
shiftH n (E (ht, hv)) = E (ht, shiftV n <$> hv)

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
eval' h (EApp f e) = app h (eval h f) (eval h e) where
  -- So yeah, supposed to be call-by-name here... relying on Haskell's laziness to delay evaluation

eval' h (ETyLam s k e) = VTyLam h s k e
eval' h (ETyApp f t) = tyapp h (eval h f) t
eval' h (ETyEqu e _) = eval h e
eval' h (EPrLam _ e) = eval h e
eval' h (EPrApp e _) = eval h e
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
eval' h (EPrj y z _ e)   -- remember: y <= z
  | null ls = VRecord []
  | otherwise = prj (eval h e) where
    ls = dom y
    prj (VRecord fs) = VRecord [(l, th) | (l, th) <- fs, l `elem` ls]
    prj v@VLabeled{} = v  -- can do dumb projections      
    prj v@VSyn{} = v   -- synthesizing fewer fields is the same as synthesizing more fields
    -- alternatively, we could do the computation here:
    -- prj (VSyn _ m) = VRecord [(l, app (eval h m) (VSing (TLab l))) | l <- ls] 
eval' h e@(EConcat x y _ _ m n) = VRecord (fields xls (eval h m) ++ fields yls (eval h n)) where
  xls = dom x
  yls = dom y
  fields _ (VRecord fs) = fs
  fields _ (VLabeled s th) = [(s, th)]
  fields ls (VSyn _ m) = [(l, app h m (VSing (TLab l))) | l <- ls]
  fields _ _ = error $ "evaluation failed: " ++ show e
eval' h (EInj _ _ _ e) = eval h e
eval' h (EBranch x y z _ f g) = VBranch (dom x) (eval h f) (eval h g)
eval' h (EAna f m) = VAna f (eval h m)
eval' h (ESyn f m) = VSyn f (eval h m)
eval' h (EIn _ e) = VIn (eval h e) -- also treating in like a constructor... probably will need that functor evidence eventually, but meh
eval' h (EOut e)
  | VIn v <- eval h e = v
eval' h@(E (ht, he)) (EFix x t e) = eval (E (ht, eval h e : he)) e
eval' _ e = error $ "evaluation failed: " ++ show e

shiftT :: Int -> Ty -> Ty
shiftT n (TVar i x k) 
  | i >= n = TVar (i + 1) x k
  | otherwise = TVar i x k
shiftT n (TThen p t) = TThen (shiftP n p) (shiftT n t) where
  shiftP n (PLeq y z) = PLeq (shiftT n y) (shiftT n z)
  shiftP n (PPlus x y z) = PPlus (shiftT n x) (shiftT n y) (shiftT n z)
shiftT n (TForall x k t) = TForall x k (shiftT (n + 1) t)
shiftT n (TLam x k t) = TLam x k (shiftT (n + 1) t)
shiftT n (TApp t u) = TApp (shiftT n t) (shiftT n u)
shiftT n (TSing t) = TSing (shiftT n t)
shiftT n (TLabeled l t) = TLabeled (shiftT n l) (shiftT n t)
shiftT n (TRow ts) = TRow (shiftT n <$> ts)
shiftT n (TPi t) = TPi (shiftT n t)
shiftT n (TSigma t) = TSigma (shiftT n t)
shiftT n (TMapFun t) = TMapFun (shiftT n t)
shiftT n (TMapArg t) = TMapArg (shiftT n t)
shiftT n t = t

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