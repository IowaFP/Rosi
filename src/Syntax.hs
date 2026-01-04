{-# LANGUAGE PatternGuards #-}
module Syntax (module Syntax) where

import Control.Monad.IO.Class
import Data.Bifunctor (first)
import Data.Generics hiding (TyCon(..), GT)
import Data.IORef
import GHC.Stack

--------------------------------------------------------------------------------
-- Top-level entities
--------------------------------------------------------------------------------

-- Qualified names: are stored in reverse order ("Data.Nat.zero" --> ["zero",
-- "Nat", "Data"]). Local names are signified with an empty list ["zero", ""].
type QName = [String]

data Program = Prog ([String], [Decl])
  deriving (Eq, Show)

data Decl = TyDecl QName Kind Ty | TmDecl QName (Maybe Ty) Term
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Goals
--
-- Goals represent problems to be solved during type inference, kind inference,
-- or predicate solving.
--------------------------------------------------------------------------------

newtype Goal t = Goal (String, IORef (Maybe t))
  deriving (Data, Typeable)

goalName :: Goal t -> String
goalName (Goal (s, _)) = s

goalRef :: Goal t -> IORef (Maybe t)
goalRef (Goal (_, r)) = r

instance Eq (Goal t) where
  Goal (x, _) == Goal (y, _) = x == y

instance Show (Goal t) where
  show (Goal (x, _)) = x

--------------------------------------------------------------------------------
-- Kinds
--------------------------------------------------------------------------------

data Kind =
    KType | KLabel | KRow Kind | KFun Kind Kind | KUnif (Goal Kind)
  deriving (Data, Eq, Show, Typeable)

flattenK :: MonadIO m => Kind -> m Kind
flattenK k@(KUnif (Goal (_, r))) =
  do mk <- liftIO $ readIORef r
     case mk of
       Nothing -> return k
       Just k' -> flattenK k'
flattenK (KRow elem) = KRow <$> flattenK elem
flattenK (KFun dom cod) = KFun <$> flattenK dom <*> flattenK cod
flattenK k = return k

data Pred =
    PLeq Ty Ty | PPlus Ty Ty Ty | PEq Ty Ty | PFold Ty
  deriving (Data, Eq, Show, Typeable)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Level = Top | Lv Int
  deriving (Eq, Data, Typeable)

instance Ord Level where
  compare Top Top = EQ
  compare Top _   = GT
  compare _ Top   = LT
  compare (Lv i) (Lv j) = compare i j

tops :: (Int -> Int -> Int) -> Level -> Level -> Level
tops f Top x = Top
tops f x Top = Top
tops f (Lv i) (Lv j) = Lv (f i j)

instance Num Level where
  (+) = tops (+)
  (*) = tops (*)
  abs Top = Top
  abs (Lv i) = Lv i
  signum Top = Lv 1
  signum (Lv x) = Lv (signum x)
  fromInteger = Lv . fromInteger
  negate Top = Top
  negate (Lv i) = Lv (negate i)

instance Show Level where
  show Top = "T"
  show (Lv i) = show i

data UVar = UV { uvShift :: Int, uvLevel :: Level, uvGoal :: Goal Ty, uvKind :: Kind }
  deriving (Data, Show, Typeable)

instance Eq UVar where
  v == v' = uvShift v == uvShift v' && goalRef (uvGoal v) == goalRef (uvGoal v')

data TyCon = Pi | Sigma | Mu (Maybe Int) | TCUnif (Goal TyCon)
  deriving (Data, Eq, Show, Typeable)

data Ty =
    TVar Int QName
  | TUnif UVar
    -- we essentially have a delayed shiftTN call here: TUnif n l g k delays a shift of variables by n
  | TFun | TThen Pred Ty | TForall String (Maybe Kind) Ty | TLam String (Maybe Kind) Ty | TApp Ty Ty
  | TLab String | TSing Ty | TLabeled Ty Ty | TRow [Ty] | TConApp TyCon Ty
  | TMapFun Ty | TCompl Ty Ty
  | TString
  -- Internals
  | TInst Insts Ty | TMapArg Ty
  deriving (Data, Eq, Show, Typeable)

data Inst = TyArg Ty | PrArg Evid
  deriving (Data, Eq, Show, Typeable)

data Insts = Known [Inst] | Unknown Int (Goal Insts)
  deriving (Data, Eq, Show, Typeable)

infixr 4 `TThen`

funTy :: Ty -> Ty -> Ty
funTy = TApp . TApp TFun

infixr 5 `funTy`

-- Does De Bruijn index n occur free in type t?
tvFreeIn :: Int -> Ty -> Bool
tvFreeIn n (TVar i _) = i == n
tvFreeIn n (TUnif u) = False
tvFreeIn n TFun = False
tvFreeIn n (TThen p t) = tvFreeIn n t
tvFreeIn n (TForall s _ t) = tvFreeIn (n + 1) t
tvFreeIn n (TLam s _ t) = tvFreeIn (n + 1) t
tvFreeIn n (TApp t u) = tvFreeIn n t || tvFreeIn n u
tvFreeIn n (TLab s) = False
tvFreeIn n (TSing t) = tvFreeIn n t
tvFreeIn n (TLabeled t u) = tvFreeIn n t || tvFreeIn n u
tvFreeIn n (TRow ts) = any (tvFreeIn n) ts
tvFreeIn n (TConApp c t) = tvFreeIn n t
tvFreeIn n (TMapFun t) = tvFreeIn n t
tvFreeIn n (TCompl t u) = tvFreeIn n t || tvFreeIn n u
tvFreeIn n TString = False

label, labeled :: Ty -> Maybe Ty
concreteLabel :: Ty -> Maybe String

label (TLabeled l _) = Just l
label _ = Nothing

concreteLabel (TLabeled (TLab s) _) = Just s
concreteLabel _                     = Nothing

labeled (TLabeled _ t) = Just t
labeled _ = Nothing

splitLabel :: Ty -> Maybe (Ty, Ty)
splitLabel (TLabeled l t) = Just (l, t)
splitLabel _              = Nothing

splitConcreteLabel :: Ty -> Maybe (String, Ty)
splitConcreteLabel (TLabeled (TLab s) t) = Just (s, t)
splitConcreteLabel _                     = Nothing

data Quant = QuForall String Kind | QuThen Pred
  deriving (Data, Eq, Show, Typeable)

quants :: Ty -> ([Quant], Ty)
quants (TForall x (Just k) t) = first (QuForall x k :) (quants t)
quants (TForall x Nothing t) = error "quants: forall without kind"
quants (TThen p t) = first (QuThen p :) (quants t)
quants t = ([], t)

quantify :: [Quant] -> Ty -> Ty
quantify [] t = t
quantify (QuForall x k : qus) t = TForall x (Just k) (quantify qus t)
quantify (QuThen p : qus) t = TThen p (quantify qus t)

insts :: Ty -> ([Insts], Ty)
insts (TInst is t) = first (is :) (insts t)
insts t = ([], t)

spine :: Ty -> (Ty, [Ty])
spine (TApp f t) = (f', ts ++ [t])
  where (f', ts) = spine f
spine t = (t, [])

flattenTC :: MonadIO m => TyCon -> m TyCon
flattenTC k@(TCUnif g) =
  do mk <- liftIO $ readIORef (goalRef g)
     case mk of
       Just k' -> flattenTC k'
       Nothing -> return k
flattenTC k = return k

-- I really need to learn SYB
flattenT :: MonadIO m => Ty -> m Ty
flattenT t@(TVar {}) = return t
flattenT t@(TUnif (UV n l g@(Goal (_, r)) k)) =
  do mt <- liftIO $ readIORef r
     case mt of
       Nothing -> TUnif . UV n l g <$> flattenK k
       Just t' -> flattenT (shiftTN 0 n t')
flattenT TFun =
  return TFun
flattenT (TThen p t) =
  TThen <$> flattenP p <*> flattenT t
flattenT (TForall x k t) =
  TForall x <$> traverse flattenK k <*> flattenT t
flattenT (TLam x k t) =
  TLam x <$> traverse flattenK k <*> flattenT t
flattenT (TApp t u) =
  TApp <$> flattenT t <*> flattenT u
flattenT t@(TLab _) = return t
flattenT (TSing t) =
  TSing <$> flattenT t
flattenT (TLabeled l t) =
  TLabeled <$> flattenT l <*> flattenT t
flattenT (TRow ts) =
  TRow <$> mapM flattenT ts
flattenT (TConApp k t) = TConApp <$> flattenTC k <*> flattenT t
flattenT (TMapFun t) =
  TMapFun <$> flattenT t
flattenT (TCompl r0 r1) =
  TCompl <$> flattenT r0 <*> flattenT r1
-- not entirely sure what *should* happen here
flattenT (TInst is t) =
  TInst <$> flattenIs is <*> flattenT t
flattenT (TMapArg t) =
  TMapArg <$> flattenT t
flattenT TString =
  return TString

flattenP :: MonadIO m => Pred -> m Pred
flattenP (PLeq z y) =
  PLeq <$> flattenT z <*> flattenT y
flattenP (PPlus x y z) =
  PPlus <$> flattenT x <*> flattenT y <*> flattenT z
flattenP (PEq t u) =
  PEq <$> flattenT t <*> flattenT u
flattenP (PFold z) =
  PFold <$> flattenT z

flattenIs :: MonadIO m => Insts -> m Insts
flattenIs is@(Unknown n (Goal (s, r))) =
  do mis <- liftIO $ readIORef r
     case mis of
       Nothing -> return is
       Just is -> flattenIs (shiftIsV [] 0 n is)
flattenIs (Known is) = Known <$> mapM flattenI is
  where flattenI (TyArg t) = TyArg <$> flattenT t
        flattenI (PrArg v) = PrArg <$> flattenV v

shiftTNV :: HasCallStack => [UVar] -> Int -> Int -> Ty -> Ty
shiftTNV _ _ 0 t = t
shiftTNV _ j n (TVar i x)
  | i >= j =
    if i + n < j
    then error "negative shift produced capture"
    else TVar (i + n) x
  | otherwise = TVar i x
shiftTNV vs _ n t@(TUnif v@(UV n' l g k))
  | v `elem` vs = t
  | otherwise = TUnif (UV (n + n') l g k)
shiftTNV vs j n (TThen p t) = TThen (shiftPNV vs j n p) (shiftTNV vs j n t)
shiftTNV vs j n (TForall x k t) = TForall x k (shiftTNV vs (j + 1) n t)
shiftTNV vs j n (TLam x k t) = TLam x k (shiftTNV vs (j + 1) n t)
shiftTNV vs j n (TApp t u) = TApp (shiftTNV vs j n t) (shiftTNV vs j n u)
shiftTNV vs j n (TSing t) = TSing (shiftTNV vs j n t)
shiftTNV vs j n (TLabeled l t) = TLabeled (shiftTNV vs j n l) (shiftTNV vs j n t)
shiftTNV vs j n (TRow ts) = TRow (shiftTNV vs j n <$> ts)
shiftTNV vs _ _ t@TFun = t
shiftTNV vs _ _ t@(TLab s) = t
shiftTNV vs j n (TConApp k t) = TConApp k (shiftTNV vs j n t)
shiftTNV vs j n (TMapFun t) = TMapFun (shiftTNV vs j n t)
shiftTNV vs j n (TMapArg t) = TMapArg (shiftTNV vs j n t)
shiftTNV vs j n (TInst is t) = TInst (shiftIsV vs j n is) (shiftTNV vs j n t) where
shiftTNV vs j n (TCompl r0 r1) = TCompl (shiftTNV vs j n r0) (shiftTNV vs j n r1)
shiftTNV _ _ _  t@TString = t
shiftTNV vs _ _ t = error $ "shiftTN: unhandled: " ++ show t

-- shiftTN j n t shifts variables at or above `j` up by `n`
shiftTN :: HasCallStack => Int -> Int -> Ty -> Ty
shiftTN = shiftTNV []

shiftIsV :: [UVar] -> Int -> Int -> Insts -> Insts
shiftIsV vs j n (Unknown n' ig) = Unknown (n + n') ig
shiftIsV vs j n (Known is) = Known (map shiftI is) where
  shiftI (TyArg t) = TyArg (shiftTNV vs j n t)
  shiftI (PrArg v) = PrArg v

shiftPNV :: [UVar] -> Int -> Int -> Pred -> Pred
shiftPNV vs j n (PEq t u) = PEq (shiftTNV vs j n t) (shiftTNV vs j n u)
shiftPNV vs j n (PLeq y z) = PLeq (shiftTNV vs j n y) (shiftTNV vs j n z)
shiftPNV vs j n (PPlus x y z) = PPlus (shiftTNV vs j n x) (shiftTNV vs j n y) (shiftTNV vs j n z)
shiftPNV vs j n (PFold z) = PFold (shiftTNV vs j n z)

shiftT :: Int -> Ty -> Ty
shiftT j = shiftTN j 1

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Const =
    CPrj | CConcat | CInj | CBranch | CSyn | CAna | CFold | CFix | CStringCat
    deriving (Data, Eq, Show, Typeable)
    -- TODO: can treat syn and ana as constants? is currently parse magic to insert identity function as default argument...
    -- TODO: can treat label and unlabel as constants with provided type argument?

data Term =
    EVar Int QName | ELam String (Maybe Ty) Term | EApp Term Term
  | ETyLam String (Maybe Kind) Term  | EPrLam Pred Term | EInst Term Insts
  | ESing Ty | ELabel (Maybe TyCon) Term Term | EUnlabel (Maybe TyCon) Term Term
  | EConst Const
  | ELet String Term Term | ECast Term Evid | ETyped Term Ty
  | EStringLit String
  deriving (Data, Eq, Show, Typeable)

shiftENV :: [UVar] -> Int -> Int -> Term -> Term
shiftENV _ _ _ e@(EVar {})   = e
shiftENV vs j n (ELam x mt e) = ELam x (shiftTNV vs j n <$> mt) (shiftENV vs j n e)
shiftENV vs j n (EApp f e)    = EApp (shiftENV vs j n f) (shiftENV vs j n e)
shiftENV vs j n (ETyLam x mk e) = ETyLam x mk (shiftENV vs (j + 1) n e)
shiftENV vs j n (EPrLam p e) = EPrLam (shiftPNV vs j n p) e
shiftENV vs j n (EInst e is) = EInst (shiftENV vs j n e) (shiftIsV [] j n is)
shiftENV vs j n (ESing t) = ESing (shiftTNV vs j n t)
shiftENV vs j n (ELabel k l e) = ELabel k (shiftENV vs j n l) (shiftENV vs j n e)
shiftENV vs j n (EUnlabel k e l) = EUnlabel k (shiftENV vs j n e) (shiftENV vs j n l)
shiftENV _ _ _ e@(EConst {}) = e
shiftENV vs j n (ELet x e f) = ELet x (shiftENV vs j n e) (shiftENV vs j n f)
shiftENV vs j n (ECast e q) = ECast (shiftENV vs j n e) q
shiftENV vs j n (ETyped e t) = ETyped e (shiftTNV vs j n t)
shiftENV _ _ _ e@(EStringLit {}) = e

shiftEN :: Int -> Int -> Term -> Term
shiftEN = shiftENV []


flattenE :: MonadIO m => Term -> m Term
flattenE = everywhereM (mkM flattenInsts) <=< everywhereM (mkM flattenT) <=< everywhereM (mkM flattenP) <=< everywhereM (mkM flattenK) <=< everywhereM (mkM flattenV) <=< everywhereM (mkM flattenTC) where
  (f <=< g) x = g x >>= f
  flattenInsts (EInst m is) = EInst m <$> flattenIs is
  flattenInsts m = return m

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
  | VEqThen Evid Evid | VEqLambda Evid | VEqForall Evid | VEqApp Evid Evid
  | VEqLabeled Evid Evid | VEqRow [Evid] | VEqSing Evid | VEqCon TyCon Evid
  | VEqMapCong Evid | VEqComplCong Evid Evid
  | VEqLeq Evid Evid | VEqPlus Evid Evid Evid
  --
  -- Fold proofs
  --
  | VFold Int
  deriving (Data, Eq, Show, Typeable)

isRefl :: Evid -> Bool
isRefl VEqRefl = True
isRefl VLeqRefl = True
isRefl v = False

foldUnary :: (Evid -> Evid) -> Evid -> Evid
foldUnary k q
  | isRefl q = q
  | otherwise = k q

foldBinary :: (Evid -> Evid -> Evid) -> Evid -> Evid -> Evid
foldBinary k q1 q2
  | isRefl q1, isRefl q2 = q1
  | otherwise = k q1 q2

flattenV :: MonadIO m => Evid -> m Evid
flattenV v@(VGoal (Goal (_, r))) =
    do w <- liftIO $ readIORef r
       case w of
         Nothing -> return v
         Just w' -> flattenV w'
flattenV (VPredEq v1 v2) =
  do v1' <- flattenV v1
     v2' <- flattenV v2
     return $ case v1' of
       VEqRefl -> v2'
       _     -> VPredEq v1' v2'
flattenV VLeqRefl = return VLeqRefl
flattenV VEqRefl = return VEqRefl
flattenV (VLeqTrans v1 v2) =
  do v1' <- flattenV v1
     v2' <- flattenV v2
     return $ case (v1', v2') of
       (VLeqRefl, _) -> v2'
       (_, VLeqRefl) -> v1'
       _          -> VLeqTrans v1' v2'
flattenV (VEqTrans v1 v2) =
  do v1' <- flattenV v1
     v2' <- flattenV v2
     return $ case (v1', v2') of
       (VEqRefl, _) -> v2'
       (_, VEqRefl) -> v1'
       _          -> VEqTrans v1' v2'
flattenV (VLeqLiftL t v) = foldUnary (VLeqLiftL t) <$> flattenV v
flattenV (VLeqLiftR v t) = foldUnary (`VLeqLiftR` t) <$> flattenV v
flattenV (VPlusLeqL v) = VPlusLeqL <$> flattenV v
flattenV (VPlusLeqR v) = VPlusLeqR <$> flattenV v
flattenV (VPlusLiftL t v) = foldUnary (VPlusLiftL t) <$> flattenV v
flattenV (VPlusLiftR v t) = foldUnary (`VPlusLiftR` t) <$> flattenV v
flattenV (VEqSym v) = foldUnary VEqSym <$> flattenV v
flattenV v@(VEqRowPermute is)
  | countUp is 0 = return VEqRefl
  | otherwise    = return v
  where countUp [] _ = True
        countUp (i : is) j = i == j && countUp is (j + 1)
flattenV (VEqThen v1 v2) = foldBinary VEqThen <$> flattenV v1 <*> flattenV v2
flattenV (VEqLambda v) = foldUnary VEqLambda <$> flattenV v
flattenV (VEqForall v) = foldUnary VEqForall <$> flattenV v
flattenV (VEqApp v1 v2) = foldBinary VEqApp <$> flattenV v1 <*> flattenV v2
flattenV (VEqLabeled v1 v2) = foldBinary VEqLabeled <$> flattenV v1 <*> flattenV v2
flattenV (VEqRow []) = return VEqRefl
flattenV (VEqRow vs) =
  do vs' <- mapM flattenV vs
     return (if all isRefl vs' then VEqRefl else VEqRow vs')
flattenV (VEqSing v) = foldUnary VEqSing <$> flattenV v
flattenV (VEqCon t v) = foldUnary (VEqCon t) <$> flattenV v
flattenV (VEqMapCong v) = foldUnary VEqMapCong <$> flattenV v
flattenV (VEqComplCong v1 v2) = foldBinary VEqComplCong <$> flattenV v1 <*> flattenV v2
flattenV (VEqLeq v1 v2) = foldBinary VEqLeq <$> flattenV v1 <*> flattenV v2
flattenV (VEqPlus v1 v2 v3) =
  do vs' <- mapM flattenV [v1, v2, v3]
     return (if all isRefl vs' then VEqRefl else VEqPlus (vs' !! 0) (vs' !! 1) (vs' !! 2))
flattenV v = return v
  -- Covers: VVar, VRefl, VLeqSimple, VPlusSimple, VEqBeta, VEqMap, VEqCompl, VEqDefn,
  -- VEqLiftTyCon, VEqTyConSing, VEqMapId, VEqMapCompose, VFold

--------------------------------------------------------------------------------
-- Type errors
--
-- Probably ought to live somewhere else
--------------------------------------------------------------------------------

data Error = ErrContextDefn QName Error | ErrContextType Ty Error | ErrContextTerm Term Error | ErrContextPred Pred Error | ErrContextOther String Error
           | ErrContextTyEq Ty Ty Error
           | ErrTypeMismatch Ty Ty Ty Ty | ErrTypeMismatchFD Pred | ErrTypeMismatchPred Pred Ty Ty | ErrKindMismatch Kind Kind
           | ErrNotEntailed [(Pred, [Pred])]
           | ErrUnboundVar QName | ErrUnboundTyVar QName | ErrDuplicateDefinition QName
           | ErrOther String
