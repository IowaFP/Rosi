module Checker.Normalize where

import Control.Monad.Reader
import Data.Bifunctor       (first)
import Data.List
import Data.Maybe

import Checker.Monad
import Checker.Utils
import Printer
import Syntax

import GHC.Stack

normalize' :: (HasCallStack, MonadCheck m) => [Eqn] -> Ty -> m (Ty, Evid)
normalize' eqns t =
  do (u, q) <- normalize eqns t
     theKCtxt <- asks kctxt
     case q of
       VEqRefl -> return (u, q)
       _       -> do trace $ "normalize (" ++ renderString (ppr t) ++ ") -->* (" ++ renderString (ppr u) ++ ")"
                     return (u, q)

etaContract :: Ty -> (Ty, Evid)
etaContract ty@(TLam s1 (Just k) (TApp t (TVar 0 s3)))
  | not (isFree [0] t) = (shiftN 0 (-1) t , VEqEta)
etaContract t = (t , VEqRefl)

normalize :: (HasCallStack, MonadCheck m) => [Eqn] -> Ty -> m (Ty, Evid)
normalize eqns t
  | Just (u, v) <- lookup t eqns =
    do (u', q) <- normalize eqns u
       return (u', VEqTrans v q)
normalize eqns t@(TVar i _) =
  do kb <- asks ((!! i) . kctxt)
     case kb of
       KBVar k _ -> return (t, VEqRefl)
       KBDefn _ def -> do (t', q) <- normalize eqns (shiftN 0 (i + 1) def)
                          return (t', VEqTrans VEqDefn q)
normalize eqns t0@(TApp (TLam x (Just k) t) u) =
  do t1 <- beta t u
     (t2, q) <- normalize eqns t1
     return (t2, VEqTrans VEqBeta q)
normalize eqns (TApp (TConApp Pi r) t) =
  do (t1, q) <- normalize eqns (TConApp Pi (TApp (TMapApp r) t))  -- To do: check kinding
     return (t1, VEqTrans (VEqLiftTyCon Pi) q)
normalize eqns (TApp (TConApp Sigma r) t) =
  do (t1, q) <- normalize eqns (TConApp Sigma (TApp (TMapApp r) t))
     return (t1, VEqTrans (VEqLiftTyCon Sigma) q)
normalize eqns (TApp (TMap f) (TRow es))
  | Just ls <- mapM label es, Just ts <- mapM labeled es =
    do (t, q) <- normalize eqns (TRow (zipWith TLabeled ls (map (TApp f) ts)))
       return (t, VEqTrans VEqMap q)
-- The next rule implements `map id == id`
normalize eqns (TApp (TMap f) z)
  | TLam _ k (TVar 0 _) <- f =
    do (z, q) <- normalize eqns z
       return (z, VEqTrans VEqMapId q)
-- The following rules (attempt to) implement `map f . map g == map (f . g)`.
-- The need for special cases arises from our various ways to represent type
-- functions: they're not all `TLam`. There are probably some cases missing: in
-- particular, I see nothing about nested maps.
normalize eqns (TApp (TMap (TLam _ _ f)) (TApp (TMap (TLam v k g)) z)) =
  do f' <- subst 0 g f
     (t, q) <- normalize eqns (TApp (TMap (TLam v k f')) z)
     return (t, VEqTrans VEqMapCompose q)
normalize eqns (TApp (TMap (TLam v (Just (KFun KType KType)) f)) (TApp (TMap TFun) z)) =
  do f' <- subst 0 (TApp TFun (TVar 0 [v, ""])) f
     (t, q) <- normalize eqns (TApp (TMap (TLam v (Just KType) f')) z)
     return (t, VEqTrans VEqMapCompose q)
normalize eqns (TApp (TMap TFun) (TApp (TMap (TLam v k f)) z)) =
  do (t, q) <- normalize eqns (TApp (TMap (TLam v k (TApp TFun f))) z)
     return (t, VEqTrans VEqMapCompose q)
normalize eqns (TApp (TMapApp (TRow es)) t)
  | Just ls <- mapM label es, Just fs <- mapM labeled es =
    do (t, q) <- normalize eqns (TRow (zipWith TLabeled ls (map (`TApp` t) fs)))
       return (t, VEqTrans VEqMapCompose q)
normalize eqns (TMapApp z) =
    do k <- kindOf z
       case k of
         KRow (KFun k1 k2) -> return (TLam "X" (Just k1) (TApp (TMap (TLam "Y" (Just (KFun k1 k2)) (TApp (TVar 0 ["Y", ""]) (TVar 1 ["X", ""])))) (shiftN 0 1 z)), VEqDefn)
         _                 -> fail ("normalize: ill-kinded " ++ show (TMapApp z))
normalize eqns (TApp t1 t2) =
  do (t1', q1) <- normalize eqns t1
     q1' <- flatten q1
     case q1' of
       VEqRefl -> do (t2', q2) <- normalize eqns t2
                     return (TApp t1 t2', VEqApp VEqRefl q2)
       _ -> do (t', q) <- normalize eqns (TApp t1' t2)
               return (t', VEqTrans (VEqApp q1 VEqRefl) q)
normalize eqns (TLabeled tl te) =
  do (tl', ql) <- normalize eqns tl
     (te', qe) <- normalize eqns te
     return (TLabeled tl' te', VEqLabeled ql qe)
normalize eqns (TRow ts) =
  do (ts', qs) <- unzip <$> mapM (normalize eqns) ts
     case mapM splitConcreteLabel ts' of
       Just ps ->
         let ps' = sortOn (fst . fst) (zip ps qs)
             is  = [fromJust (elemIndex i (map (fst . fst) ps')) | i <- map fst ps] in
         return (TRow (map (uncurry (TLabeled . TLab)) (map fst ps')), VEqRowPermute is `VEqTrans` VEqRow (map snd ps'))
       Nothing ->
         return (TRow ts', VEqRow qs)
normalize eqns (TConApp Sigma z) =
  do (z', q) <- normalize eqns z
     k <- kindOf z'
     case k of
       KRow (KRow k') ->
         do (z'', q') <- normalize eqns (TApp (TMap (TLam "x" (Just k) (TConApp Sigma (TVar 0 ["x", ""])))) z')
            return (z'', VEqTrans q q')
       _ -> return (TConApp Sigma z', VEqCon Sigma q)
normalize eqns (TConApp Pi z) =
  do (z', q) <- normalize eqns z
     k <- kindOf z'
     case k of
       KRow (KRow k') ->
         do (z'', q') <- normalize eqns (TApp (TMap (TLam "x" (Just k) (TConApp Pi (TVar 0 ["x", ""])))) z')
            return (z'', VEqTrans q q')
       _ -> return (TConApp Pi z', VEqCon Pi q)
normalize eqns (TConApp (Mu count) z) =
  do (z', q) <- normalize eqns z
     return (TConApp (Mu count) z', VEqCon (Mu count) q)
normalize eqns (TForall x (Just k) t) =
  do (t', q) <- bindTy k (normalize eqns t)
     return (TForall x (Just k) t', VEqForall q)
normalize eqns (TExists x (Just k) t) =
  do (t', q) <- bindTy k (normalize eqns t)
     return (TExists x (Just k) t', VEqExists q)
normalize eqns ty@(TLam x (Just k) t) =
  do (t',  q1) <- bindTy k (normalize eqns t)
     let (t'', q2) = etaContract (TLam x (Just k) t')
     return (t'', VEqTrans (VEqLambda q1) q2)
normalize eqns (TMap t) =
  do (t', q) <- normalize eqns t
     return (TMap t', q)
normalize eqns (TCompl x y) =
  do (x', q) <- normalize eqns x
     (y', q') <- normalize eqns y
     case (x', y') of
       (TRow xs, TRow ys)
         | Just xls <- mapM label xs
         , Just yls <- mapM label ys
         , all (`elem` xls) yls -> return (TRow [TLabeled l t | TLabeled l t <- xs, l `notElem` yls], VEqTrans (VEqComplCong q q') VEqCompl)
       _ -> return (TCompl x' y', VEqComplCong q q')
normalize eqns (TInst [] t) =
  normalize eqns t
normalize eqns t@(TInst {}) =
  do is' <- concat <$> mapM normI is
     first (TInst (map fst is')) <$> normalize eqns t'  -- TODO: should probably do something with the evidence here, but what. Not sure this case should even really be possible...
  where (is, t') = insts t
        normI (TyArg t)  = singleton . first TyArg <$> normalize eqns t
        normI (PrArg v)  = return [(PrArg v, VEqRefl)]
        normI (TyPack t) = singleton . first TyPack <$> normalize eqns t
        normI (PrPack v) = return [(PrPack v, VEqRefl)]
        normI i@(Unknown n (Goal (s, r))) =
          do minsts <- readRef r
             case minsts of
               Nothing -> return [(i, VEqRefl)]
               Just is -> concat <$> mapM normI is
normalize eqns (TThen p t) =
  do p' <- normalizeP eqns p
     (t', q) <- normalize eqns t
     return (TThen p' t', VEqThen VEqRefl q)
-- TODO: remaining homomorphic cases
normalize eqns t = return (t, VEqRefl)

normalizeP :: MonadCheck m => [Eqn] -> Pred -> m Pred -- no evidence structure for predicate equality yet soooo....
normalizeP eqns (PLeq x y)    = PLeq <$> (fst <$> normalize eqns x) <*> (fst <$> normalize eqns y)
normalizeP eqns (PPlus x y z) = PPlus <$> (fst <$> normalize eqns x) <*> (fst <$> normalize eqns y) <*> (fst <$> normalize eqns z)
normalizeP eqns (PEq t u)     = PEq <$> (fst <$> normalize' eqns t) <*> (fst <$> normalize' eqns u)
normalizeP eqns (PFold z)     = PFold <$> (fst <$> normalize' eqns z)
