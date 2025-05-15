module Checker.Utils where

import Control.Monad.Reader.Class
import Checker.Monad
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
kindOf (TApp f _) =
  do KFun _ k <- kindOf f
     return k
kindOf (TLab _) = return KLabel
kindOf (TSing _) = return KType
kindOf (TLabeled _ t) = kindOf t
kindOf (TRow []) = return $ KRow KType -- probably wrong
kindOf (TRow (t : _)) = KRow <$> kindOf t
kindOf (TPi r) =
  do KRow k <- kindOf r
     return k
kindOf (TSigma r) =
  do KRow k <- kindOf r
     return k
kindOf (TMu f)=
  do KFun k _ <- kindOf f
     return k
kindOf (TInst _ t) = kindOf t
kindOf (TMapFun f) =
  do KFun kd kc <- kindOf f
     return $ KFun (KRow kd) (KRow kc)
kindOf (TMapArg f) =
  do KRow (KFun kd kc) <- kindOf f
     return $ KFun kd (KRow kc)
kindOf (TCompl r _) = kindOf r
