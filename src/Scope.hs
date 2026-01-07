module Scope where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor
import Data.List
import Data.Maybe
import Syntax

newtype ScopeM a = ScopeM { runScope :: ReaderT ([QName], [QName]) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadReader ([QName], [QName]), MonadError Error)

runScopeM :: ScopeM a -> Either Error a
runScopeM m = runExcept (runReaderT (runScope m) ([], []))

bindVars :: ([QName], [QName]) -> ScopeM a -> ScopeM a
bindVars (tvs, vs) = local (bimap (reverse tvs ++) (reverse vs ++))

bindTyVar, bindVar :: String -> ScopeM a -> ScopeM a
bindTyVar tv = bindVars ([[tv, ""]], [])
bindVar v    = bindVars ([], [[v, ""]])

bindGTyVar, bindGVar :: QName -> ScopeM a -> ScopeM a
bindGTyVar tv = bindVars ([tv], [])
bindGVar v    = bindVars ([], [v])

lookFor :: QName -> QName -> Bool
lookFor [x] (y : ys) = x == y
lookFor xs ys        = xs == ys

tyvar :: QName -> ScopeM (Int, QName)
tyvar x = do names <- asks fst
             case findIndex (lookFor x) names of
               Nothing -> throwError (ErrUnboundTyVar x)
               Just i  -> return (i, names !! i)

var :: QName -> ScopeM Term
var x = do names <- asks snd
           case finds names of
            [] -> throwError (ErrUnboundVar x)
            (([], i) : _) ->
              return (EVar i (names !! i))
            ((xs, i) : _) ->
              do ls <- mapM (var . sing) xs
                 sel <- var ["sel", "Base", "Ro"]
                 return (foldl (\x l -> EApp (EApp sel x) l)
                               (EVar i (names !! i))
                               (reverse ls))

  where splits = [splitAt n x | n <- [0..length x]]
        finds names = [(xs, i) | (xs, x) <- splits, i <- maybeToList (findIndex (lookFor x) names)]
        sing x = [x]

class HasVars t where
  scope :: t -> ScopeM t

instance HasVars t => HasVars [t] where
  scope = mapM scope

instance HasVars t => HasVars (Maybe t) where
  scope = mapM scope

instance HasVars Ty where
  scope (TVar _ x) =

    uncurry TVar <$> tyvar x
  -- Wild assumption: scoping happens before any goals have been resolved, so
  -- I'm not going to track down the contents of the goal
  scope t@TUnif{} = return t
  scope t@TFun = return t
  scope (TThen p t) = TThen <$> scope p <*> scope t
  scope (TForall x k t) = TForall x k <$> bindTyVar x (scope t)
  scope (TLam x k t) = TLam x k <$> bindTyVar x (scope t)
  scope (TApp t u) = TApp <$> scope t <*> scope u
  scope t@TLab{} = return t
  scope (TSing t) = TSing <$> scope t
  scope (TLabeled l t) = TLabeled <$> scope l <*> scope t
  scope (TRow ts) = TRow <$> scope ts
  scope (TConApp k t) = TConApp k <$> scope t
  scope (TMapFun t) = TMapFun <$> scope t
  scope (TMapArg t) = TMapArg <$> scope t
  scope (TCompl r0 r1) = TCompl <$> scope r0 <*> scope r1
  scope TString = return TString

instance HasVars Pred where
  scope (PLeq y z) = PLeq <$> scope y <*> scope z
  scope (PPlus x y z) = PPlus <$> scope x <*> scope y <*> scope z
  scope (PEq t u) = PEq <$> scope t <*> scope u
  scope (PFold z) = PFold <$> scope z

-- There's no `instance HasVars Evid` because evidence is all constructed during
-- type checking, and so starts with de Bruijn indices.

instance HasVars Term where
  scope (EVar _ x) = var x
  scope (EConst c) = return (EConst c)
  scope (ELam x t m) = ELam x <$> traverse scope t <*> bindVar x (scope m)
  scope (EApp t u) = EApp <$> scope t <*> scope u
  scope (ETyLam x k m) = ETyLam x k <$> bindTyVar x (scope m)
  scope (ESing t) = ESing <$> scope t
  scope (ELabel k l m) = ELabel k <$> scope l <*> scope m
  scope (EUnlabel k m l) = EUnlabel k <$> scope m <*> scope l
  scope (ELet x m n) = ELet x <$> scope m <*> bindVar x (scope n)
  scope (ETyped m t) = ETyped <$> scope m <*> scope t
  scope (EInst m (Known is)) = EInst <$> scope m <*> (Known <$> mapM scopeI is) where
    scopeI (TyArg t) = TyArg <$> scope t
    scopeI (PrArg v) = return (PrArg v)
  scope (EInst m (Unknown n g)) = EInst <$> scope m <*> return (Unknown n g) -- how is this case actually possible?
  scope e@(EStringLit {}) = return e
  scope e@(EHole {}) = return e
  -- These shouldn't have been created yet
  scope EPrLam{} = error "scope: EPrLam"
  scope ECast{} = error "scope: ETyEqu"

instance HasVars Decl where
  scope (TmDecl x t m) = TmDecl x <$> (maybe id (withError . ErrContextType) t) (scope t) <*> withError (ErrContextTerm m) (scope m)
  scope (TyDecl x k t) = TyDecl x k <$> withError (ErrContextType t) (scope t)

declName (TmDecl x _ _) = x
declName (TyDecl x _ _) = x

scopeProg :: [Decl] -> ScopeM [Decl]
scopeProg [] = return []
scopeProg (d@(TmDecl x _ _) : ds) = (:) <$> scope d <*> bindGVar x (scopeProg ds)
scopeProg (d@(TyDecl x _ _) : ds) = (:) <$> scope d <*> bindGTyVar x (scopeProg ds)
