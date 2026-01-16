module Scope where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
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

bindableTyVars :: Ty -> State [Name] ()
bindableTyVarsP :: Pred -> State [Name] ()

bindableTyVars (TVar _ [v]) =
  do vs <- get
     if v `elem` vs
     then return ()
     else put (v : vs)
bindableTyVars (TVar _ qn) = return ()
bindableTyVars (TUnif {}) = return ()
bindableTyVars TFun = return ()
bindableTyVars (TThen p t) = bindableTyVarsP p >> bindableTyVars t
bindableTyVars (TForall {}) = return ()
bindableTyVars (TLam {}) = return ()
bindableTyVars (TApp t u) = bindableTyVars t >> bindableTyVars u
bindableTyVars (TLab {}) = return ()
bindableTyVars (TSing t) = bindableTyVars t
bindableTyVars (TLabeled l t) = bindableTyVars l >> bindableTyVars t
bindableTyVars (TRow ts) = mapM_ bindableTyVars ts
bindableTyVars (TConApp _ t) = bindableTyVars t
bindableTyVars (TMap t) = bindableTyVars t
bindableTyVars (TCompl z y) = bindableTyVars z >> bindableTyVars y
bindableTyVars TString = return ()
bindableTyVars (TInst is t) = error "internal type constructor in scoping"
bindableTyVars (TMapApp t) = bindableTyVars t
bindableTyVars t = error $ "<whoopsie: " ++ show t ++ ">"

bindableTyVarsP (PEq t u) = bindableTyVars t >> bindableTyVars u
bindableTyVarsP (PLeq y z) = bindableTyVars y >> bindableTyVars z
bindableTyVarsP (PPlus x y z) = mapM_ bindableTyVars [x, y, z]
bindableTyVarsP (PFold z) = bindableTyVars z

bindable :: [Name] -> Ty -> [Name]
bindable vs t = take (length ws - length vs) ws
  where ws = execState (bindableTyVars t) vs

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
  scope t@(TForall {}) =
    implicitQuantifiers t
    -- TForall x k <$> bindTyVar x (scope t)
  scope (TLam x k t) = TLam x k <$> bindTyVar x (scope t)
  scope (TApp t u) = TApp <$> scope t <*> scope u
  scope t@TLab{} = return t
  scope (TSing t) = TSing <$> scope t
  scope (TLabeled l t) = TLabeled <$> scope l <*> scope t
  scope (TRow ts) = TRow <$> scope ts
  scope (TConApp k t) = TConApp k <$> scope t
  scope (TMap t) = TMap <$> scope t
  scope (TMapApp t) = TMapApp <$> scope t
  scope (TCompl r0 r1) = TCompl <$> scope r0 <*> scope r1
  scope TString = return TString

implicitQuantifiers :: Ty -> ScopeM Ty
implicitQuantifiers t =
  do ws <- asks (map head . fst)
     let (bs, t') = tybinders t
         xs = sort $ bindable (map fst bs ++ ws) t'
     t'' <- foldr bindTyVar (scope t') (map fst bs ++ xs)
     return (rebind (bs ++ [(x, Nothing) | x <- xs]) t'')

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
  scope (TmDecl x Nothing m) =
    TmDecl x <$> pure Nothing <*> withError (ErrContextTerm m) (scope m)
  scope (TmDecl x (Just t) m) =
    TmDecl x <$>
      withError (ErrContextType t) (Just <$> implicitQuantifiers t) <*>
      withError (ErrContextTerm m) (scope m)
  scope (TyDecl x k t) =
    TyDecl x k <$>
      withError (ErrContextType t) (implicitQuantifiers t)

declName (TmDecl x _ _) = x
declName (TyDecl x _ _) = x

scopeProg :: [Decl] -> ScopeM [Decl]
scopeProg [] = return []
scopeProg (d@(TmDecl x _ _) : ds) = (:) <$> scope d <*> bindGVar x (scopeProg ds)
scopeProg (d@(TyDecl x _ _) : ds) = (:) <$> scope d <*> bindGTyVar x (scopeProg ds)

-- Testing code
deriving instance Show Error

test1 =
  runScopeM $ scope $
  TmDecl ["id"] (Just (TApp (TApp TFun (TVar (-1) ["a"])) (TVar (-1) ["a"]))) (ELam "x" Nothing (EVar (-1) ["x"]))