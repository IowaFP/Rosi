{-# LANGUAGE PatternGuards #-}
module Syntax where

import Control.Monad.IO.Class
import Data.Bifunctor (first)
import Data.Generics hiding (TyCon(..))
import Data.IORef
import GHC.Stack

newtype Program = Prog [Decl]
  deriving (Eq, Show)

data Decl = TyDecl String Kind Ty | TmDecl String Ty Term
  deriving (Eq, Show)

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
    PLeq Ty Ty | PPlus Ty Ty Ty
  deriving (Data, Eq, Show, Typeable)

newtype Goal t = Goal (String, IORef (Maybe t))
  deriving (Data, Typeable)

instance Eq (Goal t) where
  Goal (x, _) == Goal (y, _) = x == y

instance Show (Goal t) where
  show (Goal (x, _)) = x

{-------------------------------------------------------------------------------

Variables
=========

The goal, henceforth, is to use de Bruijn representation of variables. However,
for error-reporting and debugging purposes, we'll keep the original names
around. So, in `TVar Int String (Maybe Kind)`, the `Int` is the *real* identity
of the variable, and the `String` is just for printing purposes.

-------------------------------------------------------------------------------}


data Ty =
    TVar Int String (Maybe Kind)
  | TUnif Int (Goal Ty) Kind  -- we essentially have a delayed shiftTN call here: TUnif n g k delays a shift of variables by n
  | TFun | TThen Pred Ty | TForall String Kind Ty | TLam String Kind Ty | TApp Ty Ty
  | TLab String | TSing Ty | TLabeled Ty Ty | TRow [Ty] | TPi Ty | TSigma Ty
  | TMu Ty | TMapFun Ty
  -- Internals
  | TInst Insts Ty | TMapArg Ty
  deriving (Data, Eq, Show, Typeable)

-- Because I keep confusing myself:
-- MapFun : (k -> l) -> (R[k] -> R[l])
-- MapArg : R[k -> l] -> (k -> R[l])
-- Reducing MapArg to MapFun....
-- Can I do: MapArg (Z : R[k1 -> k2] == \X : k1. MapFun (\Y : k1 -> k2. Y X) Z
--
-- Need to validate rule:
--     normalize (TApp (TMapArg (TRow es)) t)
--       | Just ls <- mapM label es, Just fs <- mapM labeled es =
--         do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (`TApp` t) fs)))
--            return (t, QTrans QMapArg q)
--
-- So: TApp (TMapArg (TRow es)) t)
--    --->
--     TApp (\X. TMapFun (\Y. Y X) es)) t
--    --->
--     TMapFun (\Y. Y t) es
--    --->
--     TRow ...
-- seems to work...

-- ???

infixr 4 `TThen`

funTy :: Ty -> Ty -> Ty
funTy = TApp . TApp TFun

infixr 5 `funTy`


label, labeled :: Ty -> Maybe Ty

label (TLabeled l _) = Just l -- Just (unshift l)
label _ = Nothing

labeled (TLabeled _ t) = Just t -- Just (unshift t)
labeled _ = Nothing

splitLabel :: Ty -> Maybe (Ty, Ty)
splitLabel (TLabeled l t) = Just (l, t)
splitLabel _              = Nothing

-- I really need to learn SYB
flattenT :: MonadIO m => Ty -> m Ty
flattenT t@(TVar i v Nothing) = return t
flattenT (TVar i v (Just k)) = TVar i v . Just <$> flattenK k
flattenT t@(TUnif n g@(Goal (_, r)) k) =
  do mt <- liftIO $ readIORef r
     case mt of
       Nothing -> TUnif n g <$> flattenK k
       Just t' -> flattenT (shiftTN 0 n t')
flattenT TFun =
  return TFun
flattenT (TThen p t) =
  TThen <$> flattenP p <*> flattenT t
flattenT (TForall x k t) =
  TForall x <$> flattenK k <*> flattenT t
flattenT (TLam x k t) =
  TLam x <$> flattenK k <*> flattenT t
flattenT (TApp t u) =
  TApp <$> flattenT t <*> flattenT u
flattenT t@(TLab _) = return t
flattenT (TSing t) =
  TSing <$> flattenT t
flattenT (TLabeled l t) =
  TLabeled <$> flattenT l <*> flattenT t
flattenT (TRow ts) =
  TRow <$> mapM flattenT ts
flattenT (TPi t) =
  TPi <$> flattenT t
flattenT (TSigma t) =
  TSigma <$> flattenT t
flattenT (TMu t) =
  TMu <$> flattenT t
flattenT (TMapFun t) =
  TMapFun <$> flattenT t
-- not entirely sure what *should* happen here
flattenT (TInst g@(Unknown (Goal (_, r))) t) =
  do minsts <- liftIO $ readIORef r
     case minsts of
       Nothing -> TInst g <$> flattenT t
       Just _  -> flattenT t
flattenT (TInst (Known is) t) =
  TInst <$> (Known <$> mapM flattenI is) <*> flattenT t
  where flattenI (TyArg t) = TyArg <$> flattenT t
        flattenI (PrArg v) = return (PrArg v)
flattenT (TMapArg t) =
  TMapArg <$> flattenT t

flattenP :: MonadIO m => Pred -> m Pred
flattenP (PLeq z y) =
  PLeq <$> flattenT z <*> flattenT y
flattenP (PPlus x y z) =
  PPlus <$> flattenT x <*> flattenT y <*> flattenT z

kindOf :: HasCallStack => Ty -> Kind
kindOf (TVar _ _ (Just k)) = k
kindOf (TVar _ x Nothing) = error $ "internal: unkinded type variable " ++ x
kindOf (TUnif _ _ k) = k
kindOf TFun = KFun KType (KFun KType KType)
kindOf (TThen _ t) = kindOf t
kindOf (TForall _ _ t) = kindOf t
kindOf (TLam x k t) = KFun k (kindOf t)
kindOf (TApp f _)
  | KFun _ k <- kindOf f = k
kindOf (TLab _) = KLabel
kindOf (TSing _) = KType
kindOf (TLabeled _ t) = kindOf t
kindOf (TRow []) = KRow KType -- probably wrong
kindOf (TRow (t : _)) = KRow (kindOf t)
kindOf (TPi r)
  | KRow k <- kindOf r = k
kindOf (TSigma r)
  | KRow k <- kindOf r = k
kindOf (TMu f)
  | KFun k _ <- kindOf f = k
kindOf (TInst _ t) = kindOf t
kindOf (TMapFun f)
  | KFun kd kc <- kindOf f = KFun (KRow kd) (KRow kc)
kindOf (TMapArg f)
  | KRow (KFun kd kc) <- kindOf f = KFun kd (KRow kc)
kindOf t = error $ "internal: kindOf " ++ show t

-- shiftTN j n t shifts variables at or above `j` up by `n`
shiftTN :: HasCallStack => Int -> Int -> Ty -> Ty
shiftTN _ 0 t = t
shiftTN j n (TVar i x k)
  | i >= j =
    if i + n < j
    then error "negative shift produced capture"
    else TVar (i + n) x k
  | otherwise = TVar i x k
shiftTN _ n (TUnif n' g k) = TUnif (n + n') g k
shiftTN j n (TThen p t) = TThen (shiftPN j n p) (shiftTN j n t)
shiftTN j n (TForall x k t) = TForall x k (shiftTN (j + 1) n t)
shiftTN j n (TLam x k t) = TLam x k (shiftTN (j + 1) n t)
shiftTN j n (TApp t u) = TApp (shiftTN j n t) (shiftTN j n u)
shiftTN j n (TSing t) = TSing (shiftTN j n t)
shiftTN j n (TLabeled l t) = TLabeled (shiftTN j n l) (shiftTN j n t)
shiftTN j n (TRow ts) = TRow (shiftTN j n <$> ts)
shiftTN _ _ TFun = TFun
shiftTN j n (TPi t) = TPi (shiftTN j n t)
shiftTN j n (TSigma t) = TSigma (shiftTN j n t)
-- shiftTN j n (TShift t) = TShift (shiftTN (n - 1) j t) -- variables within the shift are larger than they appear
shiftTN j n (TMapFun t) = TMapFun (shiftTN j n t)
shiftTN j n (TMapArg t) = TMapArg (shiftTN j n t)
shiftTN j n (TInst is t) = TInst (shiftIs is) (shiftTN j n t) where
  shiftIs (Unknown ig) = Unknown ig -- FIXME
  shiftIs (Known is) = Known (map shiftI is)
  shiftI (TyArg t) = TyArg (shiftTN j n t)
  shiftT (PrArg v) = PrArg v
shiftTN _ _ t = error $ "shiftTN: unhandled: " ++ show t

shiftPN :: Int -> Int -> Pred -> Pred
shiftPN j n (PLeq y z) = PLeq (shiftTN j n y) (shiftTN j n z)
shiftPN j n (PPlus x y z) = PPlus (shiftTN j n x) (shiftTN j n y) (shiftTN j n z)

shiftT :: Int -> Ty -> Ty
shiftT j = shiftTN j 1

data Inst = TyArg Ty | PrArg Evid
  deriving (Data, Eq, Show, Typeable)

data Insts = Known [Inst] | Unknown (Goal [Inst])
  deriving (Data, Eq, Show, Typeable)

data Term =
    EVar Int String | ELam String Ty Term | EApp Term Term | ETyLam String Kind Term -- | ETyApp Term Ty
  | EInst Term Insts
  | ESing Ty | ELabel Term Term | EUnlabel Term Term
  | EPrj Ty Ty Evid Term | EConcat Ty Ty Ty Evid Term Term | EInj Ty Ty Evid Term | EBranch Ty Ty Ty Evid Term Term
  | ESyn Ty Term | EAna Ty Term | EFold Term Term Term Term
  | EIn Term Term | EOut Term | EFix String Ty Term
  | ETyped Term Ty
  -- Internals
  | EPrLam Pred Term -- | EPrApp Term Evid
  | ETyEqu Term TyEqu
  deriving (Data, Eq, Show, Typeable)

flattenE :: MonadIO m => Term -> m Term
flattenE = everywhereM (mkM flattenInsts) <=< everywhereM (mkM flattenT) <=< everywhereM (mkM flattenP) <=< everywhereM (mkM flattenK) <=< everywhereM (mkM flattenV) where
  (f <=< g) x = g x >>= f
  flattenInsts (EInst m (Unknown (Goal (_, r)))) =
    do minsts <- liftIO $ readIORef r
       case minsts of
         Nothing -> return m
         Just insts -> return (EInst m (Known insts))
  flattenInsts m = return m

data Evid =
    VVar Int   -- VVars are entirely internal, so I'll only give them de Bruijn indices
  | VGoal (Goal Evid) | VRefl | VTrans Evid Evid | VPredEq PrEqu Evid -- can this happen?
  | VLeqLiftL Ty Evid | VLeqLiftR Evid Ty | VPlusLiftL Ty Evid | VPlusLiftR Evid Ty
  | VPlusL Evid | VPlusR Evid
  | VLeqSimple [Int] | VPlusSimple [Either Int Int]
  deriving (Data, Eq, Show, Typeable)

flattenV :: MonadIO m => Evid -> m Evid
flattenV (VVar i) = return (VVar i)
flattenV v@(VGoal (Goal (_, r))) =
  do w <- liftIO $ readIORef r
     case w of
       Nothing -> return v
       Just w' -> return w'
flattenV (VTrans v w) = VTrans <$> flattenV v <*> flattenV w
flattenV (VPredEq q v) = VPredEq <$> pure (flattenQP q) <*> flattenV v
flattenV (VLeqLiftL t v) = VLeqLiftL t <$> flattenV v
flattenV (VLeqLiftR v t) = flip VLeqLiftR t <$> flattenV v
flattenV (VPlusLiftL t v) = VPlusLiftL t <$> flattenV v
flattenV (VPlusLiftR v t) = flip VPlusLiftR t <$> flattenV v
flattenV (VPlusL v) = VPlusL <$> flattenV v
flattenV (VPlusR v) = VPlusR <$> flattenV v
flattenV (VLeqSimple is) = return (VLeqSimple is)
flattenV (VPlusSimple is) = return (VPlusSimple is)
flattenV v = error $ "flattenV: unhandled: " ++ show v

-- Clearly had this idea after writing the above...
data TyCon = Pi | Sigma
  deriving (Data, Eq, Show, Typeable)

data TyEqu =
    QRefl | QSym TyEqu | QTrans TyEqu TyEqu | QBeta String Kind Ty Ty Ty -- (λ α : κ. τ) υ ≡ τ [υ / α]
  | QThen PrEqu TyEqu | QLambda TyEqu | QForall TyEqu | QApp TyEqu TyEqu | QLabeled TyEqu TyEqu | QRow [TyEqu] | QSing TyEqu
  | QMapFun | QMapArg | QCon TyCon TyEqu | QLiftTyCon TyCon Ty Ty | QTyConSing TyCon Ty Ty
  | QDefn -- like QBeta, I guess?
  deriving (Data, Eq, Show, Typeable)

flattenQ :: TyEqu -> TyEqu
flattenQ (QSym q) =
  case flattenQ q of
    QRefl -> QRefl
    q'    -> QSym q'
flattenQ (QTrans q0 q1) =
  case (flattenQ q0, flattenQ q1) of
    (QRefl, QRefl) -> QRefl
    (QRefl, q1') -> q1'
    (q0', QRefl) -> q0'
    (q0', q1') -> QTrans q0' q1'
flattenQ (QThen qp qt) =
  case (flattenQP qp, flattenQ qt) of
    (QLeq QRefl QRefl, QRefl) -> QRefl
    (QPlus QRefl QRefl QRefl, QRefl) -> QRefl
    (qp', qt') -> QThen qp' qt'
flattenQ (QLambda q) =
  case flattenQ q of
    QRefl -> QRefl
    q'    -> QLambda q'
flattenQ (QForall q) =
  case flattenQ q of
    QRefl -> QRefl
    q'    -> QForall q'
flattenQ (QApp q0 q1) =
  case (flattenQ q0, flattenQ q1) of
    (QRefl, QRefl) -> QRefl
    (q0', q1') -> QApp q0' q1'
flattenQ (QLabeled q0 q1) =
  case (flattenQ q0, flattenQ q1) of
    (QRefl, QRefl) -> QRefl
    (q0', q1') -> QLabeled q0' q1'
flattenQ (QRow []) = QRefl
flattenQ (QRow qs)
  | all (QRefl ==) qs' = QRefl
  | otherwise = QRow qs'
  where qs' = map flattenQ qs
flattenQ (QSing q) =
  case flattenQ q of
    QRefl -> QRefl
    q'    -> QSing q'
flattenQ (QCon k q) =
  case flattenQ q of
    QRefl -> QRefl
    q'    -> QCon k q'
flattenQ q = q

data PrEqu = QLeq TyEqu TyEqu | QPlus TyEqu TyEqu TyEqu
  deriving (Data, Eq, Show, Typeable)

flattenQP :: PrEqu -> PrEqu
flattenQP (QLeq qz qy) = QLeq (flattenQ qz) (flattenQ qy)
flattenQP (QPlus qx qy qz) = QPlus (flattenQ qx) (flattenQ qy) (flattenQ qz)

--

data Error = ErrContextType Ty Error | ErrContextTerm Term Error | ErrContextPred Pred Error | ErrContextOther String Error
           | ErrTypeMismatch Term Ty Ty | ErrTypeMismatchFD Pred (Maybe TyEqu) | ErrTypeMismatchPred Pred Ty Ty | ErrKindMismatch Ty Kind Kind
           | ErrNotEntailed [(Pred, [Pred])]
           | ErrUnboundVar String | ErrUnboundTyVar String
           | ErrOther String
