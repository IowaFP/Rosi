{-# LANGUAGE PatternGuards #-}
module Syntax where

import Control.Monad.IO.Class
import Data.Generics hiding (TyCon(..))
import Data.IORef

newtype Program = Prog [Decl]
  deriving (Eq, Show)

newtype Decl = Decl (String, Ty, Term)
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
    TVar Int String (Maybe Kind) | TUnif (Goal Ty) Kind | TFun | TThen Pred Ty | TForall String Kind Ty | TLam String Kind Ty | TApp Ty Ty    
  | TLab String | TSing Ty | TLabeled Ty Ty | TRow [Ty] | TPi Ty | TSigma Ty
  | TMu Ty
  -- Internals
  | TMapFun Ty | TMapArg Ty
  deriving (Data, Eq, Show, Typeable)

-- Because I keep confusing myself:
-- MapFun : (k -> l) -> R[k] -> R[l]
-- MapArg : R[k -> l] -> k -> R[l]

infixr 4 `TThen`  

quants :: Ty -> ([(String, Kind)], Ty)
quants (TForall x k t) = ((x, k) : ks, u)
  where (ks, u) = quants t
quants t = ([], t)  

funTy :: Ty -> Ty -> Ty
funTy = TApp . TApp TFun

infixr 5 `funTy`

label, labeled :: Ty -> Maybe Ty

label (TLabeled l _) = Just l
label _ = Nothing

labeled (TLabeled _ t) = Just t
labeled _ = Nothing

splitLabel :: Ty -> Maybe (Ty, Ty)
splitLabel (TLabeled l t) = Just (l, t)
splitLabel _              = Nothing

-- Yes, sadly, actually a thing

idFun :: Ty -> Bool
idFun (TLam _ k (TVar 0 _ _)) = True
idFun _ = False

-- I really need to learn SYB
flattenT :: MonadIO m => Ty -> m Ty
flattenT t@(TVar i v Nothing) = return t
flattenT (TVar i v (Just k)) = TVar i v . Just <$> flattenK k
flattenT t@(TUnif g@(Goal (_, r)) k) = 
  do mt <- liftIO $ readIORef r
     case mt of
       Nothing -> TUnif g <$> flattenK k
       Just t' -> flattenT t'
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
flattenT (TMapArg t) =
  TMapArg <$> flattenT t    

flattenP :: MonadIO m => Pred -> m Pred
flattenP (PLeq z y) =
  PLeq <$> flattenT z <*> flattenT y
flattenP (PPlus x y z) = 
  PPlus <$> flattenT x <*> flattenT y <*> flattenT z

kindOf :: Ty -> Kind
kindOf (TVar _ _ (Just k)) = k
kindOf (TVar _ x Nothing) = error $ "internal: unkinded type variable " ++ x
kindOf (TUnif _ k) = k
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
kindOf (TMapFun f) 
  | KFun kd kc <- kindOf f = KFun (KRow kd) (KRow kc)
kindOf (TMapArg f) 
  | KRow (KFun kd kc) <- kindOf f = KFun kd (KRow kc)
kindOf t = error $ "internal: kindOf " ++ show t
  
data Term =
    EVar Int String | ELam String Ty Term | EApp Term Term | ETyLam String Kind Term | ETyApp Term Ty
  | ESing Ty | ELabel Term Term | EUnlabel Term Term 
  | EPrj Ty Ty Evid Term | EConcat Ty Ty Ty Evid Term Term | EInj Ty Ty Evid Term | EBranch Ty Ty Ty Evid Term Term
  | ESyn Ty Term | EAna Ty Term | EFold Term Term Term Term
  | EIn Term Term | EOut Term | EFix String Ty Term 
  -- Internals
  | EPrLam Pred Term | EPrApp Term Evid | ETyEqu Term TyEqu
  deriving (Data, Eq, Show, Typeable)

flattenE :: MonadIO m => Term -> m Term
flattenE = everywhereM (mkM flattenT) <=< everywhereM (mkM flattenP) <=< everywhereM (mkM flattenK) <=< everywhereM (mkM flattenV) where
  (f <=< g) x = g x >>= f

insts :: Term -> Maybe ((Int, String), [Ty])
insts (EVar i x)            = Just ((i, x), [])
insts (ETyApp e t)
  | Just (v, ts) <- insts e = Just (v, ts ++ [t])
  | otherwise               = Nothing 
insts _                     = Nothing  

data Evid =
    VVar Int   -- VVars are entirely internal, so I'll only give them de Bruijn indices
  | VGoal (Goal Evid) | VRefl | VTrans Evid Evid | VPredEq PrEqu Evid -- can this happen?
  | VLeqLiftL Ty Evid | VLeqLiftR Evid Ty | VPlusLiftL Ty Evid | VPlusLiftR Evid Ty
  | VPlusL Evid | VPlusR Evid 
  | VLeqSimple [Int] | VPlusSimple [Either Int Int]
  deriving (Data, Eq, Show, Typeable)

flattenV :: MonadIO m => Evid -> m Evid
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

-- Clearly had this idea after writing the above...
data TyCon = Pi | Sigma
  deriving (Data, Eq, Show, Typeable)

data TyEqu =
    QRefl | QSym TyEqu | QTrans TyEqu TyEqu | QBeta String Kind Ty Ty Ty -- (λ α : κ. τ) υ ≡ τ [υ / α]
  | QThen PrEqu TyEqu | QLambda TyEqu | QForall TyEqu | QApp TyEqu TyEqu | QLabeled TyEqu TyEqu | QRow [TyEqu] | QSing TyEqu  
  | QMapFun | QMapArg | QCon TyCon TyEqu | QLiftTyCon TyCon Ty Ty | QTyConSing TyCon Ty Ty  
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
