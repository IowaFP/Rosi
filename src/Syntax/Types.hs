module Syntax.Types where

import Control.Monad.IO.Class
import Data.Bifunctor         (first)
import Data.Generics          hiding (Fixity (..), GT, TyCon)
import Data.IORef
import Data.Sequence          hiding (singleton)

import Syntax.Common

--------------------------------------------------------------------------------
-- Kinds
--------------------------------------------------------------------------------

data Kind =
    KType | KLabel | KRow Kind | KFun Kind Kind | KUnif (Goal Kind)
  deriving (Data, Eq, Show, Typeable)

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

data Pred =
    PLeq Ty Ty | PPlus Ty Ty Ty | PEq Ty Ty | PFold Ty
  deriving (Data, Eq, Show, Typeable)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Level = Top | Lv Int
  deriving (Eq, Data, Typeable)

instance Ord Level where
  compare Top Top       = EQ
  compare Top _         = GT
  compare _ Top         = LT
  compare (Lv i) (Lv j) = compare i j

tops :: (Int -> Int -> Int) -> Level -> Level -> Level
tops f Top x         = Top
tops f x Top         = Top
tops f (Lv i) (Lv j) = Lv (f i j)

instance Num Level where
  (+) = tops (+)
  (*) = tops (*)
  abs Top    = Top
  abs (Lv i) = Lv i
  signum Top    = Lv 1
  signum (Lv x) = Lv (signum x)
  fromInteger = Lv . fromInteger
  negate Top    = Top
  negate (Lv i) = Lv (negate i)

instance Show Level where
  show Top    = "T"
  show (Lv i) = show i

data UVar = UV { uvShift :: Int, uvLevel :: Level, uvGoal :: Goal Ty, uvKind :: Kind }
  -- we essentially have a delayed shift call here: UV n l g k delays a
  -- shift of variables by n
  deriving (Data, Show, Typeable)

instance Eq UVar where
  v == v' = goalRef (uvGoal v) == goalRef (uvGoal v')

data Expansions = Expanded Int | Unexpanded
  deriving (Data, Show)

instance Eq Expansions where
  _ == _ = True

data TyCon = Pi | Sigma | Mu Expansions | TCUnif (Goal TyCon)
  deriving (Data, Eq, Show, Typeable)

data TyOrdering = Leq | Geq
  deriving (Data, Eq, Show, Typeable)

data Ty =
    TVar Int QName | TUnif UVar
  | TForall String (Maybe Kind) Ty | TThen Pred Ty
  | TExists String (Maybe Kind) Ty | TExistsP Pred Ty
  | TLam String (Maybe Kind) Ty | TApp Ty Ty
  | TFun | TLab String | TSing Ty | TLabeled Ty Ty | TRow [Ty] | TConApp TyCon Ty
  | TMap Ty | TCompl Ty Ty
  | TString
  -- Internals and temporaries
  | TInst Insts Ty | TMapApp Ty | TPlus Ty Ty | TConOrd TyCon TyOrdering Ty
  deriving (Data, Eq, Show, Typeable)

unitTy :: Ty
unitTy = TConApp Pi (TRow [])

boolTy :: Ty
boolTy = TConApp Sigma (TRow [TLabeled (TLab "False") unitTy, TLabeled (TLab "True") unitTy])

data Inst = TyArg Ty | PrArg Evid | TyPack Ty | PrPack Evid | Unknown Int (Goal Insts)
  deriving (Data, Eq, Show, Typeable)

type Insts = [Inst]

-- data Insts = Known [Inst] | Unknown Int (Goal Insts)
--   deriving (Data, Eq, Show, Typeable)

infixr 4 `TThen`

funTy :: Ty -> Ty -> Ty
funTy = TApp . TApp TFun

infixr 5 `funTy`

(<||>) :: Applicative m => m Bool -> m Bool -> m Bool
(<||>) = liftA2 (||)

isXType :: MonadIO m => Ty -> m Bool
isXType (TVar {})       = return False
isXType (TUnif uv)      = maybe (return False) isXType =<< liftIO (readIORef (goalRef (uvGoal uv)))
isXType TFun            = return False
isXType (TForall _ _ t) = isXType t
isXType (TThen p t)     = isXPred p <||> isXType t
isXType (TExists _ _ t) = isXType t
isXType (TExistsP p t)  = isXPred p <||> isXType t
isXType (TLam _ _ t)    = isXType t
isXType (TApp t u)      = isXType t <||> isXType u
isXType (TLab {})       = return False
isXType (TSing t)       = isXType t
isXType (TLabeled l t)  = isXType l <||> isXType t
isXType (TRow ts)       = or <$> mapM isXType ts
isXType (TConApp _ t)   = isXType t
isXType (TMap t)        = isXType t
isXType (TCompl y z)    = isXType y <||> isXType z
isXType TString         = return False
isXType (TInst is t)    = return True
isXType (TMapApp t)     = isXType t
isXType (TPlus x y)     = isXType x <||> isXType y
isXType (TConOrd _ _ t) = isXType t

isXPred :: MonadIO m => Pred -> m Bool
isXPred (PLeq x y)    = isXType x <||> isXType y
isXPred (PPlus x y z) = isXType x <||> isXType y <||> isXType z
isXPred (PEq t u)     = isXType t <||> isXType u
isXPred (PFold z)     = isXType z

label, labeled :: Ty -> Maybe Ty
concreteLabel :: Ty -> Maybe String

label (TLabeled l _) = Just l
label _              = Nothing

concreteLabel (TLabeled (TLab s) _) = Just s
concreteLabel _                     = Nothing

labeled (TLabeled _ t) = Just t
labeled _              = Nothing

splitLabel :: Ty -> Maybe (Ty, Ty)
splitLabel (TLabeled l t) = Just (l, t)
splitLabel _              = Nothing

splitConcreteLabel :: Ty -> Maybe (String, Ty)
splitConcreteLabel (TLabeled (TLab s) t) = Just (s, t)
splitConcreteLabel _                     = Nothing

forallBinders, existsBinders :: Ty -> ([(Name, Maybe Kind)], Ty)
forallBinders (TForall x k t) = first ((x, k) :) (forallBinders t)
forallBinders t               = ([], t)

existsBinders (TExists x k t) = first ((x, k) :) (existsBinders t)
existsBinders t               = ([], t)

rebindForall, rebindExists :: [(Name, Maybe Kind)] -> Ty -> Ty
rebindForall = flip (foldr (uncurry TForall))
rebindExists = flip (foldr (uncurry TExists))

data Quant = QuForall String Kind | QuThen Pred | QuExists String Kind | QuExistsP Pred
  deriving (Data, Eq, Show, Typeable)

univQuants :: Ty -> ([Quant], Ty)
univQuants (TForall x (Just k) t) = first (QuForall x k :) (univQuants t)
univQuants (TForall x Nothing t)  = error "quants: forall without kind"
univQuants (TThen p t)            = first (QuThen p :) (univQuants t)
univQuants t                      = ([], t)

existQuants :: Ty -> ([Quant], Ty)
existQuants (TExists x (Just k) t) = first (QuExists x k :) (existQuants t)
existQuants (TExists x Nothing t)  = error "quants: exists without kind"
existQuants (TExistsP p t)         = first (QuExistsP p :) (existQuants t)
existQuants t                      = ([], t)

quantify :: [Quant] -> Ty -> Ty
quantify [] t                   = t
quantify (QuForall x k : qus) t = TForall x (Just k) (quantify qus t)
quantify (QuThen p : qus) t     = TThen p (quantify qus t)
quantify (QuExists x k : qus) t = TExists x (Just k) (quantify qus t)
quantify (QuExistsP p : qus) t  = TExistsP p (quantify qus t)

insts :: Ty -> (Seq Inst, Ty)
insts (TInst is t) = first (fromList is ><) (insts t)
insts t            = (Empty, t)

spine :: Ty -> (Ty, [Ty])
spine (TApp f t) = (f', ts ++ [t])
  where (f', ts) = spine f
spine t = (t, [])

--------------------------------------------------------------------------------
-- Evidence
--------------------------------------------------------------------------------

data Evid =
    VVar Int | VGoal (Goal Evid)     -- VVars are entirely internal, so I'll only give them de Bruijn indices
  | VPredEq Evid Evid             -- p1 ~ p2 /\ p1  ==>  p2
  --
  -- Leq proofs
  --
  | VLeqRefl | VLeqTrans Evid Evid
  | VLeqSimple [Int]              -- Ground evidence for r1 <= r2: indices of r1 entries in r2
  | VLeqLiftL Ty Evid             -- x <= y     ==>  f x <= f y
  | VLeqLiftR Evid Ty             -- x <= y     ==>  x t <= y t
  | VPlusLeqL Evid                -- x + y ~ z  ==>  x <= z
  | VPlusLeqR Evid                -- x + y ~ z  ==>  y <= z
  | VComplLeq Evid                -- x < y      ==>  y - x < y
  --
  -- Plus proofs
  --
  | VPlusSimple [Either Int Int]  -- Ground evidence for r1 + r2 ~ r3: indices of each r3 entry in (Left) r1 or (Right) r2
  | VPlusLiftL Ty Evid            -- x + y ~ z  ==>  f x + f y ~ f z
  | VPlusLiftR Evid Ty            -- x + y ~ z  ==>  x t + y t ~ z t
  | VPlusComplL Evid              -- x < y      ==>  (y - x) + x ~ y
  | VPlusComplR Evid              -- x < y      ==>  x + (y - x) ~ y
  --
  -- Eq proofs
  --
  -- For now, I'm only keeping enough information here to identify the rule, not
  -- to identify the rule instance. As equality proofs *other than row
  -- permutations and singleton identification* should be irrelevant at runtime,
  -- this shouldn't be able to immediately hurt us. It does make direct
  -- translation to Agda seem further and further away...
  --
  | VEqRefl | VEqTrans Evid Evid
  | VEqSym Evid
  | VEqBeta                         -- (λ α : κ. τ) υ ~ τ [υ / α]
  | VEqEta                          -- f ~ (λ α : κ. f α)
  | VEqMap                          -- ^f {t1, ..., tn} ~ {f t1, ..., f tn}
  | VEqCompl                        -- complement of known rows
  | VEqRowPermute [Int]             -- reordering of rows
  | VEqDefn                         -- Inlining definitions
  --
  | VEqLiftTyCon TyCon                -- (K r) t ~ K (r^ t), where r^ t = ^(\x. x t) r
  | VEqPlusComplL Evid                -- x + y ~ z  ==>  x ~ (z - y)
  | VEqPlusComplR Evid                -- x + y ~ z  ==>  y ~ (z - x)
  -- Functor laws for map
  | VEqMapId                        -- ^(\x.x) r ~ r
  | VEqMapCompose                   -- ^f (^g r) ~ ^(f . g) r
  -- Congruence rules
  | VEqThen Evid Evid | VEqExistsP Evid Evid
  | VEqLambda Evid | VEqForall Evid | VEqExists Evid
  | VEqApp Evid Evid | VEqLabeled Evid Evid | VEqRow [Evid] | VEqSing Evid
  | VEqCon TyCon Evid | VEqMapCong Evid | VEqComplCong Evid Evid
  | VEqLeq Evid Evid | VEqPlus Evid Evid Evid
  --
  -- Fold proofs
  --
  | VFold Int | VFoldMap Evid
  deriving (Data, Eq, Show, Typeable)

