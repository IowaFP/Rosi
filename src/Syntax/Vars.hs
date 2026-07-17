module Syntax.Vars where

import Data.List

import Syntax.Common
import Syntax.Terms
import Syntax.Types

class HasTyVars t where
  -- shiftNV vs j n t shifts variables, but *not uvars in `vs`*, at or above
  -- `j` up by `n`
  shiftNV :: [UVar] -> Int -> Int -> t -> t
  isFree :: [Int] -> t -> Bool
  subst :: MonadRef m => Int -> Ty -> t -> m t

shiftN :: HasTyVars t => Int -> Int -> t -> t
shiftN = shiftNV []

shift :: HasTyVars t => Int -> t -> t
shift = flip shiftN 1

beta :: (HasTyVars t, MonadRef m) => t -> Ty -> m t
beta x u = shiftN 0 (-1) <$> subst 0 (shift 0 u) x

instance HasTyVars Ty where
  shiftNV _ _ 0 t = t
  shiftNV _ j n (TVar i x)
    | i >= j =
      if i + n < j
      then error "negative shift produced capture"
      else TVar (i + n) x
    | otherwise = TVar i x
  shiftNV vs _ n t@(TUnif v@(UV n' l g k))
    | v `elem` vs = t
    | otherwise = TUnif (UV (n + n') l g k)
  shiftNV vs j n (TForall x k t) = TForall x k (shiftNV vs (j + 1) n t)
  shiftNV vs j n (TThen p t) = TThen (shiftNV vs j n p) (shiftNV vs j n t)
  shiftNV vs j n (TExists x k t) = TExists x k (shiftNV vs (j + 1) n t)
  shiftNV vs j n (TExistsP p t) = TExistsP (shiftNV vs j n p) (shiftNV vs j n t)
  shiftNV vs j n (TLam x k t) = TLam x k (shiftNV vs (j + 1) n t)
  shiftNV vs j n (TApp t u) = TApp (shiftNV vs j n t) (shiftNV vs j n u)
  shiftNV vs j n (TSing t) = TSing (shiftNV vs j n t)
  shiftNV vs j n (TLabeled l t) = TLabeled (shiftNV vs j n l) (shiftNV vs j n t)
  shiftNV vs j n (TRow ts) = TRow (shiftNV vs j n <$> ts)
  shiftNV vs _ _ t@TFun = t
  shiftNV vs _ _ t@(TLab s) = t
  shiftNV vs j n (TConApp k t) = TConApp k (shiftNV vs j n t)
  shiftNV vs j n (TMap t) = TMap (shiftNV vs j n t)
  shiftNV vs j n (TMapApp t) = TMapApp (shiftNV vs j n t)
  shiftNV vs j n (TInst is t) = TInst (shiftNV vs j n is) (shiftNV vs j n t)
  shiftNV vs j n (TCompl r0 r1) = TCompl (shiftNV vs j n r0) (shiftNV vs j n r1)
  shiftNV vs j n (TPlus t0 t1) = TPlus (shiftNV vs j n t0) (shiftNV vs j n t1)
  shiftNV _ _ _  t@TString = t
  shiftNV vs _ _ t = error $ "shiftTN: unhandled: " ++ show t

  isFree :: [Int] -> Ty -> Bool
  isFree ns (TVar i _)      = i `elem` ns
  isFree ns (TUnif u)       = False
  isFree ns TFun            = False
  isFree ns (TForall _ _ t) = isFree (map (1+) ns) t
  isFree ns (TThen p t)     = isFree ns p || isFree ns t
  isFree ns (TExists _ _ t) = isFree (map (1+) ns) t
  isFree ns (TExistsP p t)  = isFree ns p || isFree ns t
  isFree ns (TLam s _ t)    = isFree (map (1+) ns) t
  isFree ns (TApp t u)      = isFree ns t || isFree ns u
  isFree ns (TLab s)        = False
  isFree ns (TSing t)       = isFree ns t
  isFree ns (TLabeled t u)  = isFree ns t || isFree ns u
  isFree ns (TRow ts)       = any (isFree ns) ts
  isFree ns (TConApp c t)   = isFree ns t
  isFree ns (TMap t)        = isFree ns t
  isFree ns (TCompl t u)    = isFree ns t || isFree ns u
  isFree ns TString         = False
  isFree ns (TInst is t)    = isFree ns is || isFree ns t where
  isFree ns (TMapApp t)     = isFree ns t
  isFree ns (TPlus y z)     = isFree ns y || isFree ns z
  isFree ns (TConOrd _ _ t) = isFree ns t

  subst j t u@(TVar i _)
    | j == i = return t
    | otherwise = return u
  subst v t u@(TUnif (UV n _ (Goal (y, r)) k)) =
    do mt <- readRef r
       case mt of
         Nothing -> return u
         Just u  -> do u' <- subst v t (shiftN 0 n u)
                       -- TODO: This should be handled by promotion as well
                       writeRef r (Just (shiftN 0 (negate n) u'))
                       return u'
  subst v t TFun = return TFun
  subst v t (TThen p u) = TThen <$> subst v t p <*> subst v t u
  subst v t (TExistsP p u) = TExistsP <$> subst v t p <*> subst v t u
  subst v t (TForall w k u) = TForall w k <$> subst (v + 1) (shift 0 t) u
  subst v t (TExists w k u) = TExists w k <$> subst (v + 1) (shift 0 t) u
  subst v t (TLam w k u) = TLam w k <$> subst (v + 1) (shift 0 t) u
  subst v t (TApp u0 u1) =
    TApp <$> subst v t u0 <*> subst v t u1
  subst v t u@(TLab _) = return u
  subst v t (TSing u) = TSing <$> subst v t u
  subst v t (TLabeled l u) = TLabeled <$> subst v t l <*> subst v t u
  subst v t (TRow us) = TRow <$> mapM (subst v t) us
  subst v t (TConApp k u) = TConApp k <$> subst v t u
  subst v t (TCompl y x) = TCompl <$> subst v t y <*> subst v t x
  subst v t (TInst is u) = TInst <$> subst v t is <*> subst v t u
  subst v t (TMap f) = TMap <$> subst v t f
  subst v t (TMapApp f) = TMapApp <$> subst v t f
  subst v t TString = return TString
  subst v t u = error $ "internal: subst " ++ show v ++ " (" ++ show t ++ ") (" ++ show u ++")"

instance HasTyVars Insts where
  shiftNV vs j n = map shiftI where
    shiftI (TyArg t)       = TyArg (shiftNV vs j n t)
    shiftI (PrArg v)       = PrArg v
    shiftI (TyPack t)      = TyPack (shiftNV vs j n t)
    shiftI (PrPack v)      = PrPack v
    shiftI (Unknown n' ig) = Unknown (n + n') ig

  isFree ns = any isFreeI where
    isFreeI (TyArg t)    = isFree ns t
    isFreeI (PrArg {})   = False
    isFreeI (TyPack t)   = isFree ns t
    isFreeI (PrPack {})  = False
    isFreeI (Unknown {}) = False

  subst v t is = concat <$> mapM substI is where
    substI (TyArg u) = singleton . TyArg <$> subst v t u
    substI (PrArg v) = return [PrArg v]
    substI (TyPack u) = singleton . TyPack <$> subst v t u
    substI (PrPack v) = return [PrPack v]
    substI i@(Unknown n (Goal (_, r))) =
      do minst <- readRef r
         case minst of
           Nothing -> return [i]
           Just is -> concat <$> mapM substI is

instance HasTyVars Pred where
  shiftNV vs j n (PEq t u)     = PEq (shiftNV vs j n t) (shiftNV vs j n u)
  shiftNV vs j n (PLeq y z)    = PLeq (shiftNV vs j n y) (shiftNV vs j n z)
  shiftNV vs j n (PPlus x y z) = PPlus (shiftNV vs j n x) (shiftNV vs j n y) (shiftNV vs j n z)
  shiftNV vs j n (PFold z)     = PFold (shiftNV vs j n z)

  isFree ns (PEq t u)     = isFree ns t || isFree ns u
  isFree ns (PLeq y z)    = isFree ns y || isFree ns z
  isFree ns (PPlus x y z) = isFree ns x || isFree ns y || isFree ns z
  isFree ns (PFold z)     = isFree ns z

  subst v t (PEq u u')    = PEq <$> subst v t u <*> subst v t u'
  subst v t (PLeq y z)    = PLeq <$> subst v t y <*> subst v t z
  subst v t (PPlus x y z) = PPlus <$> subst v t x <*> subst v t y <*> subst v t z
  subst v t (PFold z)     = PFold <$> subst v t z

instance HasTyVars Term where
  shiftNV _ _ _ e@(EVar {})            = e
  shiftNV vs j n (ELam x mt e)         = ELam x (shiftNV vs j n <$> mt) (shiftNV vs j n e)
  shiftNV vs j n (EApp f e)            = EApp (shiftNV vs j n f) (shiftNV vs j n e)
  shiftNV vs j n (ETyLam x mk e)       = ETyLam x mk (shiftNV vs (j + 1) n e)
  shiftNV vs j n (EPrLam p e)          = EPrLam (shiftNV vs j n p) e
  shiftNV vs j n (EExLam xs ps y mt e) = EExLam xs (map (shiftNV vs j n) ps) y (shiftNV vs j n <$> mt) (shiftNV vs j n e)
  shiftNV vs j n (EInst e is)          = EInst (shiftNV vs j n e) (shiftNV [] j n is)
  shiftNV vs j n (ESing t)             = ESing (shiftNV vs j n t)
  shiftNV vs j n (ELabel k l e)        = ELabel k (shiftNV vs j n l) (shiftNV vs j n e)
  shiftNV vs j n (EUnlabel k e l)      = EUnlabel k (shiftNV vs j n e) (shiftNV vs j n l)
  shiftNV _ _ _ e@(EConst {})          = e
  shiftNV vs j n (ELet x e f)          = ELet x (shiftNV vs j n e) (shiftNV vs j n f)
  shiftNV vs j n (ECast e q)           = ECast (shiftNV vs j n e) q
  shiftNV vs j n (ETyped e t)          = ETyped e (shiftNV vs j n t)
  shiftNV vs j n (EInfix ops)          = error "should have desugared Einfix before now"
  shiftNV _ _ _ e@(EStringLit {})      = e
  shiftNV _ _ _ e@(EHole {})           = e

  isFree = error "isFree not implemented for terms"

  subst = error "subst not implemented for terms"

class HasUVars t where
  uvars :: MonadRef m => Level -> t -> m [UVar]

cat :: [UVar] -> [UVar] -> [UVar]
cat ts us = ts ++ filter (\u -> all (different u) ts) us where
  different t u = goalRef (uvGoal t) /= goalRef (uvGoal u)

instance HasUVars Ty where
  uvars _ (TVar {}) = return []
  uvars level (TUnif v@(UV { uvLevel = uvl, uvGoal = Goal (_, r) })) =
    do mt <- readRef r
       case mt of
         Just t -> uvars level t
         Nothing
           | uvl >= level -> return [v]
           | otherwise    -> return []
  uvars _ TFun = return []
  uvars level (TThen p t) = cat <$> uvars level p <*> uvars level t
  uvars level (TExistsP p t) = cat <$> uvars level p <*> uvars level t
  uvars level (TForall _ _ t) = uvars level t
  uvars level (TExists _ _ t) = uvars level t
  uvars level (TLam _ _ t) = uvars level t
  uvars level (TApp t u) = cat <$> uvars level t <*> uvars level u
  uvars _ (TLab {}) = return []
  uvars level (TSing t) = uvars level t
  uvars level (TLabeled l t) = cat <$> uvars level l <*> uvars level t
  uvars level (TRow ts) = foldl cat [] <$> mapM (uvars level) ts
  uvars level (TConApp k t) = uvars level t
  uvars level (TMap t) = uvars level t
  uvars level (TInst is t) = cat <$> uvars level is <*> uvars level t where

  uvars level (TMapApp t) = uvars level t
  uvars _ TString = return []
  uvars level (TCompl t1 t2) = cat <$> uvars level t1 <*> uvars level t2

instance HasUVars [Inst] where
  uvars level is = foldl cat [] <$> mapM iuvars is where
    iuvars (TyArg t)    = uvars level t
    iuvars (PrArg {})   = return []
    iuvars (TyPack t)   = uvars level t
    iuvars (PrPack {})  = return []
    iuvars (Unknown {}) = return []

instance HasUVars Pred where
  uvars level (PEq t u)     = cat <$> uvars level t <*> uvars level u
  uvars level (PLeq y z)    = cat <$> uvars level y <*> uvars level z
  uvars level (PPlus x y z) = cat <$> (cat <$> uvars level x <*> uvars level y) <*> uvars level z
  uvars level (PFold z)     = uvars level z
