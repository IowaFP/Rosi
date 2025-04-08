{-# LANGUAGE PatternGuards #-}
module Syntax where

import Control.Monad.IO.Class
import Data.Bifunctor (first)
import Data.Generics hiding (TyCon(..))
import Data.IORef
import GHC.Stack

data Program = Prog ([String], [Decl])
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
    PLeq Ty Ty | PPlus Ty Ty Ty | PEq Ty Ty
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
  | TFun | TThen Pred Ty | TForall String (Maybe Kind) Ty | TLam String (Maybe Kind) Ty | TApp Ty Ty
  | TLab String | TSing Ty | TLabeled Ty Ty | TRow [Ty] | TPi Ty | TSigma Ty
  | TMu Ty | TMapFun Ty
  | TCompl Ty Ty
  -- Internals
  | TInst Insts Ty | TMapArg Ty
  deriving (Data, Eq, Show, Typeable)

data Inst = TyArg Ty | PrArg Evid
  deriving (Data, Eq, Show, Typeable)

data Insts = Known [Inst] | Unknown Int (Goal [Inst])
  deriving (Data, Eq, Show, Typeable)

infixr 4 `TThen`

funTy :: Ty -> Ty -> Ty
funTy = TApp . TApp TFun

infixr 5 `funTy`

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
flattenT (TPi t) =
  TPi <$> flattenT t
flattenT (TSigma t) =
  TSigma <$> flattenT t
flattenT (TMu t) =
  TMu <$> flattenT t
flattenT (TMapFun t) =
  TMapFun <$> flattenT t
flattenT (TCompl r0 r1) =
  TCompl <$> flattenT r0 <*> flattenT r1
-- not entirely sure what *should* happen here
flattenT (TInst g@(Unknown n (Goal (s, r))) t) =
  do minsts <- liftIO $ readIORef r
     case minsts of
       Nothing -> TInst g <$> flattenT t
       Just insts  -> flattenT (TInst (shiftIs 0 n (Known insts)) t)
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
flattenP (PEq t u) =
  PEq <$> flattenT t <*> flattenT u

kindOf :: HasCallStack => Ty -> Kind
kindOf (TVar _ _ (Just k)) = k
kindOf (TVar _ x Nothing) = error $ "internal: unkinded type variable " ++ x
kindOf (TUnif _ _ k) = k
kindOf TFun = KFun KType (KFun KType KType)
kindOf (TThen _ t) = kindOf t
kindOf (TForall _ _ t) = kindOf t
kindOf (TLam x (Just k) t) = KFun k (kindOf t)
kindOf (TLam x Nothing t) = error "kindOf: TLam without kind"
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
kindOf (TCompl r _) = kindOf r
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
shiftTN _ _ t@TFun = t
shiftTN _ _ t@(TLab s) = t
shiftTN j n (TPi t) = TPi (shiftTN j n t)
shiftTN j n (TSigma t) = TSigma (shiftTN j n t)
shiftTN j n (TMu t) = TMu (shiftTN j n t)
shiftTN j n (TMapFun t) = TMapFun (shiftTN j n t)
shiftTN j n (TMapArg t) = TMapArg (shiftTN j n t)
shiftTN j n (TInst is t) = TInst (shiftIs j n is) (shiftTN j n t) where
shiftTN j n (TCompl r0 r1) = TCompl (shiftTN j n r0) (shiftTN j n r1)
shiftTN _ _ t = error $ "shiftTN: unhandled: " ++ show t

shiftIs :: Int -> Int -> Insts -> Insts
shiftIs j n (Unknown n' ig) = Unknown (n + n') ig
shiftIs j n (Known is) = Known (map shiftI is) where
  shiftI (TyArg t) = TyArg (shiftTN j n t)
  shiftI (PrArg v) = PrArg v

shiftPN :: Int -> Int -> Pred -> Pred
shiftPN j n (PLeq y z) = PLeq (shiftTN j n y) (shiftTN j n z)
shiftPN j n (PPlus x y z) = PPlus (shiftTN j n x) (shiftTN j n y) (shiftTN j n z)

shiftEN :: Int -> Int -> Term -> Term
shiftEN _ _ e@(EVar {})   = e
shiftEN j n (ELam x mt e) = ELam x (shiftTN j n <$> mt) (shiftEN j n e)
shiftEN j n (EApp f e)    = EApp (shiftEN j n f) (shiftEN j n e)
shiftEN j n (ETyLam x mk e) = ETyLam x mk (shiftEN (j + 1) n e)
shiftEN j n (EPrLam p e) = EPrLam (shiftPN j n p) e
shiftEN j n (EInst e is) = EInst (shiftEN j n e) (shiftIs j n is)
shiftEN j n (ESing t) = ESing (shiftTN j n t)
shiftEN j n (ELabel l e) = ELabel (shiftEN j n l) (shiftEN j n e)
shiftEN j n (EUnlabel e l) = EUnlabel (shiftEN j n e) (shiftEN j n l)
shiftEN _ _ e@(EConst {}) = e
shiftEN j n (ESyn t e) = ESyn (shiftTN j n t) e
shiftEN j n (EAna t e) = EAna (shiftTN j n t) e
shiftEN j n (EFold e f g h) = EFold (shiftEN j n e) (shiftEN j n f) (shiftEN j n g) (shiftEN j n h)
shiftEN j n (ECast e q) = ECast (shiftEN j n e) q
shiftEN j n (ETyped e t) = ETyped e (shiftTN j n t)

shiftT :: Int -> Ty -> Ty
shiftT j = shiftTN j 1

data Const =
    CPrj | CConcat | CInj | CBranch | CIn | COut | CFix
    deriving (Data, Eq, Show, Typeable)
    -- TODO: can treat syn and ana as constants? is currently parse magic to insert identity function as default argument...
    -- TODO: can treat label and unlabel as constants with provided type argument?

data Term =
    EVar Int String | ELam String (Maybe Ty) Term | EApp Term Term
  | ETyLam String (Maybe Kind) Term  | EPrLam Pred Term | EInst Term Insts
  | ESing Ty | ELabel Term Term | EUnlabel Term Term
  | EConst Const
  | ESyn Ty Term | EAna Ty Term | EFold Term Term Term Term
  | ECast Term Evid | ETyped Term Ty
  deriving (Data, Eq, Show, Typeable)

flattenE :: MonadIO m => Term -> m Term
flattenE = everywhereM (mkM flattenInsts) <=< everywhereM (mkM flattenT) <=< everywhereM (mkM flattenP) <=< everywhereM (mkM flattenK) <=< everywhereM (mkM flattenV) where
  (f <=< g) x = g x >>= f
  flattenInsts (EInst m (Unknown n (Goal (_, r)))) =
    do minsts <- liftIO $ readIORef r
       case minsts of
         Nothing -> return m
         Just insts -> return (EInst m (shiftIs 0 n (Known insts)))
  flattenInsts m = return m

data Evid =
    VVar Int | VGoal (Goal Evid)     -- VVars are entirely internal, so I'll only give them de Bruijn indices
  | VPredEq Evid Evid             -- p1 ~ p2 /\ p1  ==>  p2

  -- Leq proofs
  | VLeqRefl | VLeqTrans Evid Evid
  | VLeqSimple [Int]              -- Ground evidence for r1 <= r2: indices of r1 entries in r2
  | VLeqLiftL Ty Evid             -- x <= y     ==>  f x <= f y
  | VLeqLiftR Evid Ty             -- x <= y     ==>  x t <= y t
  | VPlusLeqL Evid                -- x + y ~ z  ==>  x <= z
  | VPlusLeqR Evid                -- x + y ~ z  ==>  y <= z
  | VComplLeq Evid                -- x < y      ==>  y - x < y
  -- Plus proofs
  | VPlusSimple [Either Int Int]  -- Ground evidence for r1 + r2 ~ r3: indices of each r3 entry in (Left) r1 or (Right) r2
  | VPlusLiftL Ty Evid            -- x + y ~ z  ==>  f x + f y ~ f z
  | VPlusLiftR Evid Ty            -- x + y ~ z  ==>  x t + y t ~ z t
  | VPlusComplL Evid              -- x < y      ==>  (y - x) + x ~ y
  | VPlusComplR Evid              -- x < y      ==>  x + (y - x) ~ y
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
  | VEqMap                          -- ^f {t1, ..., tn} ~ {f t1, ..., f tn}
  | VEqCompl                        -- complement of known rows
  | VEqRowPermute [Int]             -- reordering of rows
  | VEqDefn                         -- Inlining definitions
  --
  | VEqLiftTyCon TyCon                -- (K r) t ~ K (r^ t), where r^ t = ^(\x. x t) r
  | VEqTyConSing TyCon                -- {l := t} ~ K {l := t}
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
  deriving (Data, Eq, Show, Typeable)

data TyCon = Pi | Sigma | Mu
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
         Just w' -> return w'
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
       _          -> VLeqTrans v1' v2'
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
  -- VEqLiftTyCon, VEqTyConSing, VEqMapId, VEqMapCompose,

--

data Error = ErrContextType Ty Error | ErrContextTerm Term Error | ErrContextPred Pred Error | ErrContextOther String Error
           | ErrTypeMismatch Term Ty Ty | ErrTypeMismatchFD Pred (Maybe Evid) | ErrTypeMismatchPred Pred Ty Ty | ErrKindMismatch Ty Kind Kind
           | ErrNotEntailed [(Pred, [Pred])]
           | ErrUnboundVar String | ErrUnboundTyVar String
           | ErrOther String
