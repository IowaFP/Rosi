{-# LANGUAGE TypeApplications #-}
module Syntax.Goals where

import Data.Generics hiding (TyCon)
import Data.List

import Syntax.Common
import Syntax.Terms
import Syntax.Types
import Syntax.Vars

class HasGoals t where
  flatten :: MonadRef m => t -> m t

instance HasGoals Kind where
  flatten k@(KUnif (Goal (_, r))) =
    do mk <- readRef r
       case mk of
         Nothing -> return k
         Just k' -> flatten k'
  flatten (KRow elem) = KRow <$> flatten elem
  flatten (KFun dom cod) = KFun <$> flatten dom <*> flatten cod
  flatten k = return k

instance HasGoals TyCon where
  flatten k@(TCUnif g) =
    do mk <- readRef (goalRef g)
       case mk of
         Just k' -> flatten k'
         Nothing -> return k
  flatten k = return k

instance HasGoals Ty where
  -- I really need to learn SYB
  flatten t@(TVar {}) = return t
  flatten t@(TUnif (UV n l g@(Goal (_, r)) k)) =
    do mt <- readRef r
       case mt of
         Nothing -> TUnif . UV n l g <$> flatten k
         Just t' -> flatten (shiftN 0 n t')
  flatten TFun =
    return TFun
  flatten (TForall x k t) =
    TForall x <$> traverse flatten k <*> flatten t
  flatten (TThen p t) =
    TThen <$> flatten p <*> flatten t
  flatten (TExists x k t) =
    TExists x <$> traverse flatten k <*> flatten t
  flatten (TExistsP p t) =
    TExistsP <$> flatten p <*> flatten t
  flatten (TLam x k t) =
    TLam x <$> traverse flatten k <*> flatten t
  flatten (TApp t u) =
    TApp <$> flatten t <*> flatten u
  flatten t@(TLab _) = return t
  flatten (TSing t) =
    TSing <$> flatten t
  flatten (TLabeled l t) =
    TLabeled <$> flatten l <*> flatten t
  flatten (TRow ts) =
    TRow <$> mapM flatten ts
  flatten (TConApp k t) = TConApp <$> flatten k <*> flatten t
  flatten (TMap t) =
    TMap <$> flatten t
  flatten (TCompl r0 r1) =
    TCompl <$> flatten r0 <*> flatten r1
  flatten TString =
    return TString
  flatten (TInst is t) =
    TInst <$> flatten is <*> flatten t
  flatten (TMapApp t) =
    TMapApp <$> flatten t
  flatten (TPlus t u) =
    TPlus <$> flatten t <*> flatten u
  flatten (TConOrd k rel t) =
    TConOrd k rel <$> flatten t

instance HasGoals Pred where
  flatten (PLeq z y) =
    PLeq <$> flatten z <*> flatten y
  flatten (PPlus x y z) =
    PPlus <$> flatten x <*> flatten y <*> flatten z
  flatten (PEq t u) =
    PEq <$> flatten t <*> flatten u
  flatten (PFold z) =
    PFold <$> flatten z


instance HasGoals Insts where
  flatten is = concat <$> mapM flattenI is where
    flattenI (TyArg t)  = singleton . TyArg <$> flatten t
    flattenI (PrArg v)  = singleton . PrArg <$> flatten v
    flattenI (TyPack t) = singleton . TyPack <$> flatten t
    flattenI (PrPack v) = singleton . PrPack <$> flatten v
    flattenI i@(Unknown n (Goal (s, r))) =
      do mis <- readRef r
         case mis of
           Nothing -> return [i]
           Just is -> flatten (shiftNV [] 0 n is)

instance HasGoals Term where
  flatten = everywhereM (mkM flattenInsts) <=<
            everywhereM (mkM (flatten @Ty)) <=<
            everywhereM (mkM (flatten @Pred)) <=<
            everywhereM (mkM (flatten @Kind)) <=<
            everywhereM (mkM (flatten @Evid)) <=<
            everywhereM (mkM (flatten @TyCon))
    where
      (f <=< g) x = g x >>= f
      flattenInsts (EInst m is) =
        do is' <- flatten is
           case is' of
             [] -> return m
             _  -> return (EInst m is')
      flattenInsts m            = return m

isRefl :: Evid -> Bool
isRefl VEqRefl  = True
isRefl VLeqRefl = True
isRefl v        = False

foldUnary :: (Evid -> Evid) -> Evid -> Evid
foldUnary k q
  | isRefl q = q
  | otherwise = k q

foldBinary :: (Evid -> Evid -> Evid) -> Evid -> Evid -> Evid
foldBinary k q1 q2
  | isRefl q1, isRefl q2 = q1
  | otherwise = k q1 q2

instance HasGoals Evid where
  flatten v@(VGoal (Goal (_, r))) =
      do w <- readRef r
         case w of
           Nothing -> return v
           Just w' -> flatten w'
  flatten (VPredEq v1 v2) =
    do v1' <- flatten v1
       v2' <- flatten v2
       return $ case v1' of
         VEqRefl -> v2'
         _       -> VPredEq v1' v2'
  flatten VLeqRefl = return VLeqRefl
  flatten VEqRefl = return VEqRefl
  flatten (VLeqTrans v1 v2) =
    do v1' <- flatten v1
       v2' <- flatten v2
       return $ case (v1', v2') of
         (VLeqRefl, _) -> v2'
         (_, VLeqRefl) -> v1'
         _             -> VLeqTrans v1' v2'
  flatten (VEqTrans v1 v2) =
    do v1' <- flatten v1
       v2' <- flatten v2
       return $ case (v1', v2') of
         (VEqRefl, _) -> v2'
         (_, VEqRefl) -> v1'
         _            -> VEqTrans v1' v2'
  flatten (VLeqLiftL t v) = foldUnary (VLeqLiftL t) <$> flatten v
  flatten (VLeqLiftR v t) = foldUnary (`VLeqLiftR` t) <$> flatten v
  flatten (VPlusLeqL v) = VPlusLeqL <$> flatten v
  flatten (VPlusLeqR v) = VPlusLeqR <$> flatten v
  flatten (VPlusLiftL t v) = foldUnary (VPlusLiftL t) <$> flatten v
  flatten (VPlusLiftR v t) = foldUnary (`VPlusLiftR` t) <$> flatten v
  flatten (VEqSym v) = foldUnary VEqSym <$> flatten v
  flatten v@(VEqRowPermute is)
    | countUp is 0 = return VEqRefl
    | otherwise    = return v
    where countUp [] _       = True
          countUp (i : is) j = i == j && countUp is (j + 1)
  flatten (VEqThen v1 v2) = foldBinary VEqThen <$> flatten v1 <*> flatten v2
  flatten (VEqLambda v) = foldUnary VEqLambda <$> flatten v
  flatten (VEqForall v) = foldUnary VEqForall <$> flatten v
  flatten (VEqExists v) = foldUnary VEqExists <$> flatten v
  flatten (VEqApp v1 v2) = foldBinary VEqApp <$> flatten v1 <*> flatten v2
  flatten (VEqLabeled v1 v2) = foldBinary VEqLabeled <$> flatten v1 <*> flatten v2
  flatten (VEqRow []) = return VEqRefl
  flatten (VEqRow vs) =
    do vs' <- mapM flatten vs
       return (if all isRefl vs' then VEqRefl else VEqRow vs')
  flatten (VEqSing v) = foldUnary VEqSing <$> flatten v
  flatten (VEqCon t v) = foldUnary (VEqCon t) <$> flatten v
  flatten (VEqMapCong v) = foldUnary VEqMapCong <$> flatten v
  flatten (VEqComplCong v1 v2) = foldBinary VEqComplCong <$> flatten v1 <*> flatten v2
  flatten (VEqLeq v1 v2) = foldBinary VEqLeq <$> flatten v1 <*> flatten v2
  flatten (VEqPlus v1 v2 v3) =
    do vs' <- mapM flatten [v1, v2, v3]
       return (if all isRefl vs' then VEqRefl else VEqPlus (vs' !! 0) (vs' !! 1) (vs' !! 2))
  flatten v = return v
    -- Covers: VVar, VRefl, VLeqSimple, VPlusSimple, VEqBeta, VEqMap, VEqCompl, VEqDefn,
    -- VEqLiftTyCon, VEqTyConSing, VEqMapId, VEqMapCompose, VFold
