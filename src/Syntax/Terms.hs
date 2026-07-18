module Syntax.Terms where

import Data.Generics hiding (Fixity (..), GT, TyCon)

import Syntax.Common
import Syntax.Types

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Const =
    CPrj | CConcat | CInj | CBranch | CSyn | CAna | CFold | CFix | CStringCat | CStringEq
    deriving (Data, Eq, Show, Typeable)
    -- TODO: can treat syn and ana as constants? is currently parse magic to insert identity function as default argument...
    -- TODO: can treat label and unlabel as constants with provided type argument?

data Term =
    EVar Int QName | ELam String (Maybe Ty) Term | EApp Term Term
  | ETyLam String (Maybe Kind) Term  | EPrLam Pred Term
  | EExLam [(String, Maybe Kind)] [Pred] String (Maybe Ty) Term
  | EInst Term Insts
  | ESing Ty | ELabel (Maybe TyCon) Term Term | EUnlabel (Maybe TyCon) Term Term
  | EConst Const | EInfix [EInfixToken]
  | ELet String Term Term | ECast Term Evid | ETyped Term Ty
  | EStringLit String | EHole String
  deriving (Data, Eq, Show, Typeable)

data EInfixToken = Operator EOp | Operand AppTerm
  deriving (Data, Eq, Show)

instance Ord EOp where
  compare (Op _ _ (Just f1)) (Op _ _ (Just f2)) = compare f1 f2
  compare l r                                   = error $ "internal: tried to compare EInfixTokens which are not operators" ++ show l ++ ", " ++ show r

explicitApp :: EInfixToken
explicitApp = Operator $ Op (-1) ["__Apply"] (Just (Fixity InfixL 10))

data EOp = Op Int QName (Maybe Fixity)
  deriving (Data, Eq, Show)

data AppTerm = AType Ty | ATerm Term
  deriving (Data, Eq, Show)

hasHoles :: Term -> Bool
hasHoles (EHole {})         = True
hasHoles (ELam _ _ e)       = hasHoles e
hasHoles (EApp f e)         = hasHoles f || hasHoles e
hasHoles (ETyLam _ _ e)     = hasHoles e
hasHoles (EPrLam _ e)       = hasHoles e
hasHoles (EExLam _ _ _ _ e) = hasHoles e
hasHoles (EInst e _)        = hasHoles e
hasHoles (ELabel _ l e)     = hasHoles l || hasHoles e
hasHoles (EUnlabel _ e l)   = hasHoles e || hasHoles l
hasHoles (ELet _ e f)       = hasHoles e || hasHoles f
hasHoles (ECast e _)        = hasHoles e
hasHoles (ETyped e _)       = hasHoles e
hasHoles _                  = False -- covers: EVar, ESing, EConst

--------------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------------

data Program = Prog ([String], [Decl])
  deriving (Eq, Show)

data Decl = TyDecl QName Kind Ty | TmDecl QName (Maybe Ty) Term (Maybe Fixity)
  deriving (Eq, Show)

