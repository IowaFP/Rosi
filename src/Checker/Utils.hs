module Checker.Utils where

import Control.Monad.Reader.Class

import Checker.Monad
import Checker.Types
import Syntax

kindOf :: MonadCheck m => Ty -> m Kind
kindOf (TVar i _) = flattenK =<< asks (kbKind . (!! i) . kctxt)
kindOf (TUnif (UV {uvKind = k})) = flattenK k
kindOf TFun = return $ KFun KType (KFun KType KType)
kindOf (TThen _ t) = kindOf t
kindOf (TForall _ (Just k) t) = bindTy k $ kindOf t
kindOf (TForall _ Nothing t) = error "kindOf: unkinded forall"
kindOf (TLam x (Just k) t) = KFun k <$> (bindTy k $ kindOf t)
kindOf (TLam x Nothing t) = error "kindOf: unkinded lambda"
kindOf t@(TApp f _) =
  do k' <- kindOf f
     case k' of
       KFun _ k -> return k
       _ -> fail ("kindOf: ill-kinded " ++ show t)
kindOf (TLab _) = return KLabel
kindOf (TSing _) = return KType
kindOf (TLabeled _ t) = kindOf t
kindOf (TRow []) =
  do k <- kindGoal "e"
     return $ KRow k
kindOf (TRow (t : _)) = KRow <$> kindOf t
kindOf (TConApp Pi r) =
  do KRow k <- kindOf r
     return k
kindOf (TConApp Sigma r) =
  do KRow k <- kindOf r  -- TODO: what if pattern matching fails?
     return k
kindOf (TConApp Mu f)=
  do KFun k _ <- kindOf f
     return k
kindOf (TConApp (TCUnif g) t) =
  do mk <- readRef (goalRef g)
     case mk of
       Just k -> kindOf (TConApp k t)
       Nothing -> fail "kindOf: unknown constructor"
kindOf (TInst _ t) = kindOf t
kindOf (TMapFun f) =
  do KFun kd kc <- kindOf f
     return $ KFun (KRow kd) (KRow kc)
kindOf (TMapArg f) =
  do KRow (KFun kd kc) <- kindOf f
     return $ KFun kd (KRow kc)
kindOf (TCompl r _) = kindOf r
kindOf TString = return KType
