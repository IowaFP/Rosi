module Scope where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor
import Data.List
import Syntax

newtype ScopeM a = ScopeM { runScope :: ReaderT ([String], [String]) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadReader ([String], [String]), MonadError Error)

runScopeM :: ScopeM a -> Either Error a
runScopeM m = runExcept (runReaderT (runScope m) ([], []))

bindVars :: ([String], [String]) -> ScopeM a -> ScopeM a
bindVars (tvs, vs) = local (bimap (reverse tvs ++) (reverse vs ++))

bindTyVar, bindVar :: String -> ScopeM a -> ScopeM a
bindTyVar tv = bindVars ([tv], [])
bindVar v = bindVars ([], [v])

generic :: (([String], [String]) -> [String]) -> (String -> Error) -> String -> ScopeM Int
generic sel err x = do mi <- asks (elemIndex x . sel)
                       case mi of
                         Nothing -> throwError (err x)
                         Just i  -> return i

var, tyvar :: String -> ScopeM Int
var = generic snd ErrUnboundVar
tyvar = generic fst ErrUnboundTyVar

class HasVars t where
  scope :: t -> ScopeM t

instance HasVars t => HasVars [t] where
  scope = mapM scope

instance HasVars Ty where
  scope (TVar _ x mk) =
    TVar <$> tyvar x <*> pure x <*> pure mk
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
  scope (TPi t) = TPi <$> scope t
  scope (TSigma t) = TSigma <$> scope t
  scope (TMu t) = TMu <$> scope t
  scope (TMapFun t) = TMapFun <$> scope t
  scope (TMapArg t) = TMapArg <$> scope t

instance HasVars Pred where
  scope (PLeq y z) = PLeq <$> scope y <*> scope z
  scope (PPlus x y z) = PPlus <$> scope x <*> scope y <*> scope z

-- There's no `instance HasVars Evid` because evidence is all constructed during
-- type checking, and so starts with de Bruijn indices.

instance HasVars Term where
  scope (EVar _ x) = EVar <$> var x <*> pure x
  scope (ELam x t m) = ELam x <$> scope t <*> bindVar x (scope m)
  scope (EApp t u) = EApp <$> scope t <*> scope u
  scope (ETyLam x k m) = ETyLam x k <$> bindTyVar x (scope m)
  scope (ESing t) = ESing <$> scope t
  scope (ELabel l m) = ELabel <$> scope l <*> scope m
  scope (EUnlabel m l) = EUnlabel <$> scope m <*> scope l
  scope (EPrj y z v m) = EPrj <$> scope y <*> scope z <*> pure v <*> scope m
  scope (EConcat x y z v m n) = EConcat <$> scope x <*> scope y <*> scope z <*> pure v <*> scope m <*> scope n
  scope (EInj y z v m) = EInj <$> scope y <*> scope z <*> pure v <*> scope m
  scope (EBranch x y z v m n) = EBranch <$> scope x <*> scope  y <*> scope z <*> pure v <*> scope m <*> scope n
  scope (ESyn t m) = ESyn <$> scope t <*> scope m
  scope (EAna t m) = EAna <$> scope t <*> scope m
  scope (EFold m n1 n2 n3) = EFold <$> scope m <*> scope n1 <*> scope n2 <*> scope n3
  scope (ETyped m t) = ETyped <$> scope m <*> scope t
  scope (EInst m (Known is)) = EInst <$> scope m <*> (Known <$> mapM scopeI is) where
    scopeI (TyArg t) = TyArg <$> scope t
    scopeI (PrArg v) = return (PrArg v)
  scope (EInst m (Unknown g)) = EInst <$> scope m <*> return (Unknown g) -- how is this case actually possible?
  -- These shouldn't have been created yet
  scope EPrLam{} = error "scope: EPrLam"
  scope ETyEqu{} = error "scope: ETyEqu"

instance HasVars Decl where
  scope (TmDecl x t m) = TmDecl x <$> withError (ErrContextType t) (scope t) <*> withError (ErrContextTerm m) (scope m)
  scope (TyDecl x k t) = TyDecl x k <$> withError (ErrContextType t) (scope t)

scopeProg :: [Decl] -> ScopeM [Decl]
scopeProg [] = return []
scopeProg (d@(TmDecl x _ _) : ds) = (:) <$> scope d <*> bindVar x (scopeProg ds)
scopeProg (d@(TyDecl x _ _) : ds) = (:) <$> scope d <*> bindTyVar x (scopeProg ds)

instance HasVars Program where
  scope (Prog ds) = Prog <$> scopeProg ds
