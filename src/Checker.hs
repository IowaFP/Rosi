{-# LANGUAGE GeneralisedNewtypeDeriving, PatternGuards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fmap" #-}
module Checker where

import Control.Monad (foldM, liftM, liftM2, liftM3, mapAndUnzipM, mplus, replicateM, unless, when, zipWithM)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
    ( MonadWriter(listen, tell), WriterT(..), censor )
import Data.IORef
import Data.List (elemIndex, nub)

import Syntax

trace, trace' :: MonadIO m => String -> m ()
-- trace = liftIO . putStrLn 
trace _ = return ()
trace' = liftIO . putStrLn

readRef :: MonadIO m => IORef a -> m a
readRef = liftIO . readIORef

writeRef :: MonadIO m => IORef a -> a -> m ()
writeRef x = liftIO . writeIORef x

newRef :: MonadIO m => a -> m (IORef a)
newRef = liftIO . newIORef

-- expect t actual expected

data TypeError = ErrContextType Ty TypeError | ErrContextTerm Term TypeError | ErrContextPred Pred TypeError | ErrContextOther String TypeError 
               | ErrTypeMismatch Term Ty Ty | ErrTypeMismatchFD Pred (Maybe TyEqu) | ErrTypeMismatchPred Pred Ty Ty | ErrKindMismatch Ty Kind Kind
               | ErrNotEntailed [(Pred, [Pred])]
               | ErrUnboundTyVar String | ErrUnboundVar String | ErrOther String

kindGoal :: MonadIO m => String -> m Kind
kindGoal s =
  do kr <- newRef Nothing
     return (KUnif (Goal ("k$" ++ s, kr)))

  -- Note: just returning a `Ty` here out of convenience; it's always an exactly the input `Ty`.
expectK :: (MonadError TypeError m, MonadIO m) => Ty -> Kind -> Kind -> m Ty
expectK t actual expected =
  do i <- expectKR t actual expected
     when (i /= 0) $
       kindMismatch t actual expected
     return t

expectKR :: (MonadError TypeError m, MonadIO m) => Ty -> Kind -> Kind -> m Int
expectKR t actual expected =
  do mi <- unifyK actual expected
     case mi of
       Nothing -> kindMismatch t actual expected
       Just i  -> return i

unifyK :: MonadIO m => Kind -> Kind -> m (Maybe Int)
unifyK KType KType = return (Just 0)
unifyK KLabel KLabel = return (Just 0)
unifyK (KUnif (Goal (_, r))) expected =
  do mActual <- readRef r
     case mActual of
       Nothing -> writeRef r (Just expected) >> return (Just 0)
       Just actual' -> unifyK actual' expected
unifyK actual (KUnif (Goal (_, r))) =
  do mExpected <- readRef r
     case mExpected of
       Nothing -> writeRef r (Just actual) >> return (Just 0)
       Just expected' -> unifyK actual expected'
unifyK (KRow rActual) (KRow rExpected) = unifyK rActual rExpected
unifyK (KRow rActual) kExpected = ((1+) <$>) <$> unifyK rActual kExpected
unifyK (KFun dActual cActual) (KFun dExpected cExpected) =
  (*&*) <$> unifyK dActual dExpected <*> unifyK cActual cExpected where
  Just 0 *&* Just 0 = Just 0
  _ *&* _ = Nothing
unifyK _ _ =
  return Nothing

kindMismatch :: (MonadError TypeError m, MonadIO m) => Ty -> Kind -> Kind -> m a
kindMismatch t actual expected =
  do actual' <- flattenK actual
     expected' <- flattenK expected
     throwError (ErrKindMismatch t actual' expected')     

checkTy' :: Term -> Ty -> Kind -> CheckM Ty
checkTy' e t k = withError (ErrContextTerm e) (checkTy t k)

checkTy :: Ty -> Kind -> CheckM Ty
checkTy (TVar v Nothing) expected =
  do k <- asks (lookup v . kctxt)
     case k of
       Nothing -> throwError (ErrUnboundTyVar v)
       Just k' -> expectK (TVar v (Just k')) k' expected
checkTy (TVar v (Just kv)) expected =
  do k <- asks (lookup v . kctxt)
     case k of
       Nothing -> throwError (ErrUnboundTyVar v)
       Just k' -> 
        do expectK (TVar v (Just k')) kv k'
           expectK (TVar v (Just k')) k' expected       
checkTy t@(TUnif _ k) expected = expectK t k expected
checkTy TFun expected = expectK TFun (KFun KType (KFun KType KType)) expected
checkTy (TThen pi t) expected =
  TThen <$>
    checkPred pi <*>
    checkTy t expected
checkTy (TForall x k t) expected =
  TForall x k <$> bindTy x k (checkTy t expected)
checkTy t@(TLam x k u) expected =
  do k' <- kindGoal "d"
     expectK t (KFun k k') expected
     TLam x k <$> bindTy x k (checkTy u k')
checkTy (TApp t u) expected =
  do -- Step 1: work out the function's kind, including potential lifting
     kfun <- kindGoal "f"
     t' <- checkTy t kfun
     kdom <- kindGoal "d"
     kcod <- kindGoal "c"
     n <- expectKR t kfun (KFun kdom kcod)
     -- Step 2: work out the argument's kind, including potential lifting
     karg <- kindGoal "a"
     u' <- checkTy u karg
     m <- expectKR u karg kdom
     -- If lifting is involved, this should also be reflected in the expected kind
     expectK (TApp t u) (foldr ($) kcod (replicate (n + m) KRow)) expected
     -- Step 3: build exciting result type
     return (TApp (foldr ($) t' (replicate n TMapArg ++ replicate m TMapFun)) u')

checkTy t@(TLab _) expected = expectK t KLabel expected
checkTy t@(TSing l) expected =
  do expectK t KType expected
     TSing <$> checkTy l KLabel
checkTy t@(TLabeled l u) expected =
  TLabeled <$>
    checkTy l KLabel <*>
    checkTy u expected
checkTy t@(TRow [TLabeled lt et]) expected =
  do kelem <- kindGoal "e"
     expectK t (KRow kelem) expected
     lt' <- checkTy lt KLabel
     et' <- checkTy et kelem
     return (TRow [TLabeled lt' et'])
checkTy t@(TRow ts) expected =
  -- Note, building in our row theory here...
  do kelem <- kindGoal "e"
     expectK t (KRow kelem) expected
     case mapM label ts of
       Nothing -> fail "explicit rows must be built from explicitly labeled types"
       Just ls | nub ls /= ls -> fail "explicit row labels must be unique"
               | otherwise -> return ()
     TRow <$> mapM (\(TLabeled l u) -> TLabeled l <$> checkTy u kelem) ts
checkTy (TPi r) expected = TPi <$> checkTy r (KRow expected)
checkTy (TSigma r) expected = TSigma <$> checkTy r (KRow expected)
checkTy (TMu f) expected = TMu <$> checkTy f (KFun expected expected)
checkTy t@(TMapFun f) expected =
  do kdom <- kindGoal "d"
     kcod <- kindGoal "c"
     expectK t (KFun kdom (KRow kcod)) expected
     TMapFun <$> checkTy f (KFun kdom kcod)
checkTy t@(TMapArg f) expected =
  do kdom <- kindGoal "d"
     kcod <- kindGoal "e"
     expectK t (KFun (KRow kcod) (KRow kcod)) expected
     TMapFun <$> checkTy f (KFun kdom kcod)

checkPred :: Pred -> CheckM Pred
checkPred p@(PLeq y z) =
  withError (ErrContextPred p)  $
  do kelem <- kindGoal "e"
     PLeq <$> checkTy y (KRow kelem)
          <*> checkTy z (KRow kelem)
checkPred p@(PPlus x y z) =
  withError (ErrContextPred p) $
  do kelem <- kindGoal "e"
     PPlus <$> checkTy x (KRow kelem)
           <*> checkTy y (KRow kelem)
           <*> checkTy z (KRow kelem)

-- Terms

newtype CSt = CSt { next :: Int }
data CIn = CIn { kctxt :: KCtxt, tctxt :: TCtxt, pctxt :: PCtxt }
type Problem = (CIn, Pred, IORef (Maybe Evid))
newtype COut = COut { goals :: [Problem] }
  deriving (Semigroup, Monoid)


newtype CheckM a = CM (WriterT COut (ReaderT CIn (StateT CSt (ExceptT TypeError IO))) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader CIn, MonadState CSt, MonadWriter COut, MonadError TypeError)

instance MonadFail CheckM where
  fail s = throwError (ErrOther s)

runCheckM m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (CIn [] [] [])) (CSt 0)) where
  CM m' = andSolve m

runCheckM' g m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (CIn [] g [])) (CSt 0)) where
  CM m' = andSolve m

bindTy :: String -> Kind -> CheckM a -> CheckM a
bindTy x k = local (\env -> env { kctxt = (x, k) : kctxt env })

bind :: String -> Ty -> CheckM a -> CheckM a
bind x t = local (\env -> env { tctxt = (x, t) : tctxt env })

assume :: String -> Pred -> CheckM a -> CheckM a
assume x g = local (\env -> env { pctxt = (x, g) : pctxt env })

require :: Pred -> IORef (Maybe Evid) -> CheckM ()
require p r =
  do cin <- ask
     tell (COut [(cin, p, r)])

fresh :: String -> CheckM String
fresh x = do i <- gets next
             modify (\st -> st { next = i + 1 })
             return (x ++ '$' : show i)

--

expectT :: Term -> Ty -> Ty -> CheckM TyEqu
expectT m actual expected =
  do b <- unify actual expected
     case b of
       Nothing -> typeMismatch m actual expected
       Just q  -> return q

unify :: Ty -> Ty -> CheckM (Maybe TyEqu)
unify (TVar x _) (TVar y _)
  | x == y = return (Just QRefl)
unify (TUnif (Goal (_, r)) k) expected =
  do mt <- readRef r
     case mt of
       Just t -> unify t expected
       Nothing ->
         do expected' <- flattenT expected
            expectK expected' (kindOf expected') k
            writeRef r (Just expected')
            return (Just QRefl)
unify actual (TUnif (Goal (_, r)) k) =
  do mt <- readRef r
     case mt of
       Just t -> unify actual t
       Nothing ->
         do actual' <- flattenT actual
            expectK actual' (kindOf actual') k
            writeRef r (Just actual')
            return (Just QRefl)
unify TFun TFun = return (Just QRefl)
unify (TThen pa ta) (TThen px tx) =
  liftM2 QThen <$> unifyP pa px <*> unify ta tx
unify a@(TForall xa ka ta) x@(TForall xx kx tx) =  -- To do: equate variables? For now, assuming they're identical
  do ksUnify <- liftIO $ unifyK ka kx
     if xa == xx && ksUnify == Just 0
     then liftM QForall <$> unify ta tx
     else do trace $ "1 incoming unification failure: " ++ show a ++ ", " ++ show x
             return Nothing
unify a@(TLam xa ka ta) x@(TLam xx kx tx) =  -- To do: as above.  Note: this case is missing from higher.pdf
  do ksUnify <- liftIO $ unifyK ka kx
     if xa == xx && ksUnify == Just 0
     then liftM QLambda <$> unify ta tx
     else do trace $ "2 incoming unification failure: " ++ show a ++ ", " ++ show x
             return Nothing
unify actual@(TApp {}) expected = unifyNormalizing actual expected
unify actual expected@(TApp {}) = unifyNormalizing actual expected
unify (TLab sa) (TLab sx)
  | sa == sx = return (Just QRefl)
unify (TSing ta) (TSing tx) =
  liftM QSing <$> unify ta tx
unify (TLabeled la ta) (TLabeled lx tx) =
  liftM2 QLabeled <$> unify la lx <*> unify ta tx
unify (TRow ra) (TRow rx) =
  liftM QRow <$> (sequence <$> zipWithM unify ra rx)
unify (TPi ra) (TPi rx) =
  liftM (QCon Pi) <$> unify ra rx
unify (TPi r) u 
  | TRow [t] <- r = liftM (QTrans (QTyConSing Pi (TRow [t]) u)) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify (TPi r') u
         Nothing -> 
           do expectK r k (KRow (kindOf u))
              writeRef tr (Just (TRow [u]))
              return (Just (QTyConSing Pi (TRow [u]) u))
unify t (TPi r) 
  | TRow [u] <- r = liftM (`QTrans` QTyConSing Pi t (TRow [u])) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify t (TPi r')
         Nothing -> 
           do expectK r k (KRow (kindOf t))
              writeRef tr (Just (TRow [t]))
              return (Just (QTyConSing Pi (TRow [t]) t))  
unify (TSigma ra) (TSigma rx) =
  liftM (QCon Sigma) <$> unify ra rx
unify (TSigma r) u
  | TRow [t] <- r = liftM (QTrans (QTyConSing Sigma (TRow [t]) u)) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify (TSigma r') u
         Nothing -> 
           do expectK r k (KRow (kindOf u))
              writeRef tr (Just (TRow [u]))
              return (Just (QTyConSing Sigma (TRow [u]) u))
unify t (TSigma r)
  | TRow [u] <- r = liftM (`QTrans` QTyConSing Sigma t (TRow [u])) <$> unify t u
  | TUnif (Goal (_, tr)) k <- r =
    do mt <- readRef tr
       case mt of
         Just r' -> unify t (TSigma r')
         Nothing -> 
           do expectK r k (KRow (kindOf t))
              writeRef tr (Just (TRow [t]))
              return (Just (QTyConSing Sigma (TRow [t]) t))  
unify a@(TMapFun f) x@(TMapFun g) =
  do q <- unify f g
     case q of
       Just QRefl -> return (Just QRefl)
       Just _     -> return (Just QMapFun)
       Nothing    -> 
        do trace $ "3 incoming unification failure: " ++ show a ++ ", " ++ show x
           return Nothing
unify a@(TMapArg f) x@(TMapArg g) =
  do q <- unify f g
     case q of
       Just QRefl -> return (Just QRefl)
       Just _     -> return (Just QMapFun)
       Nothing    -> 
        do trace $ "4 incoming unification failure: " ++ show a ++ ", " ++ show x
           return Nothing
unify t u = 
  do do trace $ "5 incoming unification failure: " ++ show t ++ ", " ++ show u
     return Nothing

-- Assumption: at least one of actual or expected is a `TApp`
unifyNormalizing actual expected =
  do (actual', qa) <- normalize actual
     (expected', qe) <- normalize expected
     case (flattenQ qa, flattenQ qe) of
       (QRefl, QRefl) ->
         case (actual', expected') of
           (TApp fa aa, TApp fx ax) ->
             liftM2 QApp <$> unify fa fx <*> unify aa ax
           (TApp (TMapFun fa) (TRow ts), tx) ->
             do unify (TRow [TApp fa ta | ta <- ts]) tx
                return (Just QMapFun)
           (TApp (TMapFun fa) ra, TRow []) ->
             do unify ra (TRow [])
                return (Just QMapFun)
           (TApp (TMapFun fa) ra, TRow xs@(tx:_)) -> 
             do gs <- replicateM (length xs) (typeGoal' "t" (kindOf tx))
                unify ra (TRow gs)
                sequence_ [unify (TApp fa ta) tx | (ta, tx) <- zip gs xs]
                return (Just QMapFun)
           _ -> do trace $ "6 incoming unification failure: " ++ show actual' ++ ", " ++ show expected'
                   return Nothing
       (qa, qe) ->
         liftM (QTrans qa . (`QTrans` QSym qe)) <$>
         unify actual' expected'

-- Sigh

subst :: String -> Ty -> Ty -> CheckM Ty
subst v t (TVar w k)
  | v == w = return t
  | otherwise = return (TVar w k)
subst v t u@(TUnif (Goal (y, r)) k) =
  do mt <- readRef r
     case mt of
       Nothing -> return u
       Just u  -> do u' <- subst v t u
                     writeRef r (Just u')
                     return u'
subst v t TFun = return TFun
subst v t (TThen p u) = TThen <$> substp v t p <*> subst v t u
subst v t u0@(TForall w k u)
  | v == w = return u0
  | otherwise = TForall w k <$> subst v t u
subst v t u0@(TLam w k u)
  | v == w = return u0
  | otherwise = TLam w k <$> subst v t u
subst v t (TApp u0 u1) =
  TApp <$> subst v t u0 <*> subst v t u1
subst v t u@(TLab _) = return u
subst v t (TSing u) = TSing <$> subst v t u
subst v t (TLabeled l u) = TLabeled <$> subst v t l <*> subst v t u
subst v t (TRow us) = TRow <$> mapM (subst v t) us
subst v t (TPi u) = TPi <$> subst v t u
subst v t (TSigma u) = TSigma <$> subst v t u
subst v t (TMapFun f) = TMapFun <$> subst v t f
subst v t (TMapArg f) = TMapArg <$> subst v t f
subst v t u = error $ "internal: subst " ++ show v ++ " (" ++ show t ++ ") (" ++ show u ++")"

substp :: String -> Ty -> Pred -> CheckM Pred
substp v t (PLeq y z) = PLeq <$> subst v t y <*> subst v t z
substp v t (PPlus x y z) = PPlus <$> subst v t x <*> subst v t y <*> subst v t z

normalize :: Ty -> CheckM (Ty, TyEqu)
normalize (TApp (TLam x k t) u) =
  do t1 <- subst x u t
     (t2, q) <- normalize t1
     return (t2, QTrans (QBeta x k t u t1) q)
normalize (TApp (TPi r) t) =
  do (t1, q) <- normalize (TPi (TApp (TMapArg r) t))  -- To do: check kinding
     return (t1, QTrans (QLiftTyCon Pi r t) q)
normalize (TApp (TSigma r) t) =
  do (t1, q) <- normalize (TSigma (TApp (TMapArg r) t))
     return (t1, QTrans (QLiftTyCon Sigma r t) q)
normalize (TApp (TMapFun f) (TRow es))
  | Just ls <- mapM label es, Just ts <- mapM labeled es =
    do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (TApp f) ts)))
       return (t, QTrans QMapFun q)
normalize (TApp (TMapFun f) z)
  | TLam v k (TVar w _) <- f
  , v == w =
    do (z, q) <- normalize z
       return (z, QTrans QMapFun q)
  | TLam v k t <- f
  , KRow (KFun _ _) <- kindOf z =
    do (t, q) <- normalize =<< subst v (TMapArg z) t
       return (t, QTrans QMapFun q)
normalize (TApp (TMapArg (TRow es)) t)
  | Just ls <- mapM label es, Just fs <- mapM labeled es =
    do (t, q) <- normalize (TRow (zipWith TLabeled ls (map (`TApp` t) fs)))
       return (t, QTrans QMapArg q)
normalize (TApp t1 t2) =
  do (t1', q1) <- normalize t1
     case flattenQ q1 of
       QRefl -> do (t2', q2) <- normalize t2
                   return (TApp t1 t2', QApp QRefl q2)
       _ -> do (t', q) <- normalize (TApp t1' t2)
               return (t', QTrans (QApp q1 QRefl) q)
normalize (TLabeled tl te) =
  do (tl', ql) <- normalize tl
     (te', qe) <- normalize te
     return (TLabeled tl' te', QLabeled ql qe)
normalize (TRow ts) =
  do (ts', qs) <- unzip <$> mapM normalize ts
     return (TRow ts', QRow qs)
normalize (TSigma z) =
  do (z', q) <- normalize z
     return (TSigma z', QCon Sigma q)

normalize t = return (t, QRefl)

unifyP :: Pred -> Pred -> CheckM (Maybe PrEqu)
unifyP (PLeq y z) (PLeq y' z') = liftM2 QLeq <$> unify y y' <*> unify z z'
unifyP (PPlus x y z) (PPlus x' y' z') = liftM3 QPlus <$> unify x x' <*> unify y y' <*> unify z z'

typeMismatch :: Term -> Ty -> Ty -> CheckM a
typeMismatch m actual expected =
  do actual' <- flattenT actual
     expected' <- flattenT expected
     throwError (ErrTypeMismatch m actual' expected')

wrap :: TyEqu -> Term -> Term
wrap q t = case flattenQ q of
             QRefl -> t
             q'    -> ETyEqu t q'

typeGoal :: String -> CheckM Ty
typeGoal s =
  (`TUnif` KType) . Goal . ("t$" ++ s,) <$> newRef Nothing

typeGoal' :: String -> Kind -> CheckM Ty
typeGoal' s k =
  (`TUnif` k) . Goal . ("t$" ++ s,) <$> newRef Nothing

checkTerm' :: Term -> Ty -> CheckM Term
checkTerm' e t = checkTerm e =<< flattenT t

lookupVar :: String -> CheckM Ty
lookupVar v =
  do g <- asks tctxt
     case lookup v g of
       Nothing -> throwError (ErrUnboundVar v)
       Just actual -> return actual

inst :: Term -> Ty -> Ty -> CheckM Term
inst e (TForall x k t) expected =
  do u <- typeGoal' "t" k
     t' <- subst x u t
     inst (ETyApp e u) t' expected
inst e (TThen p t) expected =
  do vr <- newRef Nothing
     require p vr
     inst (EPrApp e (VGoal (Goal ("v", vr)))) t expected
inst e t expected = flip wrap e <$> expectT e t expected

checkTerm :: Term -> Ty -> CheckM Term
checkTerm e0@(ETyLam v k e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TForall v k tcod) expected
     wrap q . ETyLam v k <$> bindTy v k (checkTerm' e tcod)
checkTerm e (TForall v k t) =
  ETyLam v k <$> bindTy v k (checkTerm e t)
checkTerm e0@(EPrLam v p e) expected =
  do tcod <- typeGoal "cod"
     q <- expectT e0 (TThen p tcod) expected
     wrap q . EPrLam v p <$> assume v p (checkTerm' e tcod)
checkTerm e (TThen p t) =
  do pvar <- fresh "v"
     EPrLam pvar p <$> assume pvar p (checkTerm e t)
checkTerm e@(EVar v) expected = flip (inst (EVar v)) expected =<< flattenT =<< lookupVar v
checkTerm e0@(ELam v t e) expected =
  do tcod <- typeGoal "cod"
     t' <- checkTy' e0 t KType
     q <- expectT e0 (funTy t' tcod) expected
     wrap q . ELam v t' <$> bind v t' (checkTerm' e tcod)
checkTerm e0@(EApp f e) expected =
  do tdom <- typeGoal "dom"
     EApp <$>
       checkTerm f (funTy tdom expected) <*>
       checkTerm' e tdom
checkTerm e0@(ETyApp e t) expected
  | Just (v, ts) <- insts e0 =
    do u <- flattenT =<< lookupVar v
       let (ks, actual) = quants u
       when (length ks < length ts) $
         fail $ "too many type arguments to " ++ v ++ " : " ++ show u
       ts' <- zipWithM (\t (_, k) -> checkTy' e0 t k) ts ks
       actual' <- foldM (\u' ((x, _), t) -> subst x t u') actual (zip ks ts')
       inst (foldl (\e t -> ETyApp e t) (EVar v) ts')
            (foldr (\(x, k) t -> TForall x k t) actual' (drop (length ts) ks))
            expected
  | otherwise =
    -- Saddest of faces...
    do et <- typeGoal "t"
       e' <- checkTerm e et
       et' <- flattenT et
       case et' of
         TForall x k u ->
           do u' <- subst x t u
              q <- expectT e0 u' expected
              return (wrap q (ETyApp e' t))
         _ -> fail $ "in " ++ show e0 ++ ": expected " ++ show et' ++ " to be a quantified type"
checkTerm e0@(EPrApp e p) expected =
  fail "unimplemented"
checkTerm e0@(ESing t) expected =
  do q <- expectT e0 (TSing t) expected
     wrap q . ESing <$> checkTy' e0 t KLabel
checkTerm e0@(ELabeled el e) expected =
  do tl <- typeGoal' "l" KLabel
     t <- typeGoal "t"
     q <- expectT e0 (TLabeled tl t) expected
     wrap q <$>
       (ELabeled <$> checkTerm' el (TSing tl) <*> checkTerm' e t)
checkTerm e0@(EUnlabel e el) expected =
  do tl <- typeGoal' "l" KLabel
     el' <- checkTerm el (TSing tl)
     e' <- checkTerm' e (TLabeled tl expected)
     return (EUnlabel e' el')
checkTerm e0@(EPrj y z v@(VGoal (Goal (_, r))) e) expected =
  do y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TPi y') expected
     e' <- checkTerm e (TPi z')
     require (PLeq y' z') r
     return (wrap q (EPrj y' z' v e'))  -- but let's go ahead and flatten this term...
checkTerm (EPrj {}) _ =
  fail "unimplemented: prj with non-goal evidence"
checkTerm e0@(EConcat x y z v@(VGoal (Goal (_, r))) m n) expected =
  do x' <- checkTy x (KRow (kindOf expected))
     y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TPi z') expected
     m' <- checkTerm m (TPi x')
     n' <- checkTerm n (TPi y')
     require (PPlus x' y' z') r
     return (wrap q (EConcat x' y' z' v m' n'))
checkTerm (EConcat {}) _ =
  fail "unimplemented: ++ with non-goal evidence"
checkTerm e0@(EInj y z v@(VGoal (Goal (_, r))) e) expected =
  do y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     q <- expectT e0 (TSigma z') expected
     e' <- checkTerm e (TSigma y')
     require (PLeq y' z') r
     return (wrap q (EPrj y' z' v e'))  -- but let's go ahead and flatten this term...
checkTerm (EInj {}) _ =
  fail "unimplemented: inj with non-goal evidence"
checkTerm e0@(EBranch x y z v@(VGoal (Goal (_, r))) m n) expected =
  do x' <- checkTy x (KRow (kindOf expected))
     y' <- checkTy y (KRow (kindOf expected))
     z' <- checkTy z (KRow (kindOf expected))
     t <- typeGoal "t"
     q <- expectT e0 (funTy (TSigma z') t) expected
     t' <- flattenT t
     m' <- checkTerm m (funTy (TSigma x') t')
     n' <- checkTerm n (funTy (TSigma y') t')
     require (PPlus x' y' z') r
     return (wrap q (EBranch x' y' z' v m' n'))
checkTerm (EBranch {}) _ =
  fail "unimplemented: ++ with non-goal evidence"
checkTerm e0@(EAna phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     t <- typeGoal "t"
     q <- expectT e0 (TSigma (TApp (TMapFun phi') r) `funTy` t) expected
     EAna phi' <$> checkTerm e (TForall "l" KLabel $ TForall "u" k $ TForall "y1" (KRow k) $ TForall "z" (KRow k) $ TForall "y2" (KRow k) $
                                PPlus (TVar "y1" (Just (KRow k))) (TRow [TLabeled (TVar "l" (Just KLabel)) (TVar "u" (Just k))]) (TVar "z" (Just (KRow k))) `TThen`
                                PPlus (TVar "z" (Just (KRow k))) (TVar "y2" (Just (KRow k))) r `TThen`
                                TSing (TVar "l" (Just KLabel)) `funTy` TApp phi' (TVar "u" (Just k)) `funTy` t)
checkTerm e0@(ESyn phi e) expected =
  do k <- kindGoal "k"
     phi' <- checkTy' e0 phi (KFun k KType)
     r <- typeGoal' "r" (KRow k)
     q <- expectT e0 (TPi (TApp (TMapFun phi') r)) expected
     ESyn phi' <$> checkTerm e (TForall "l" KLabel $ TForall "u" k $ TForall "y1" (KRow k) $ TForall "z" (KRow k) $ TForall "y2" (KRow k) $
                                PPlus (TVar "y1" (Just (KRow k))) (TRow [TLabeled (TVar "l" (Just KLabel)) (TVar "u" (Just k))]) (TVar "z" (Just (KRow k))) `TThen`
                                PPlus (TVar "z" (Just (KRow k))) (TVar "y2" (Just (KRow k))) r `TThen`
                                TSing (TVar "l" (Just KLabel)) `funTy` TApp phi' (TVar "u" (Just k)))

solve :: (CIn, Pred, IORef (Maybe Evid)) -> CheckM Bool
solve (cin, p, r) =
  local (const cin) $ 
  do mv <- everything =<< flattenP p
     case mv of
       Just v -> writeRef r (Just v) >> return True
       Nothing -> return False

  where

  (<|>) :: CheckM (Maybe a) -> CheckM (Maybe a) -> CheckM (Maybe a)
  m <|> n = maybe n (return . Just) =<< m

  infixr 2 <|>

  everything p = 
    prim p <|> mapFunApp p <|> mapArgApp p <|> byAssump (pctxt cin) p

  match :: Pred -> (String, Pred) -> CheckM (Maybe Evid)
  match (PLeq y z) (v, PLeq y' z')
    | y == y' && z == z' = return (Just (VVar v))
  match p@(PPlus x y z) (v, q@(PPlus x' y' z'))
    | xEqual && yEqual = forceFD z z'
    | xEqual && zEqual = forceFD y y'
    | yEqual && zEqual = forceFD x x'
    | otherwise = return Nothing

    where xEqual = x == x'
          yEqual = y == y'
          zEqual = z == z'

          forceFD t t' =
            do q <- unify t t'
               case flattenQ <$> q of
                 Just QRefl -> return (Just (VVar v))
                 _          -> fundeps p q

  match p q = return Nothing

  -- question to self: why do I have both the `fundeps` error and the `force` error?

  fundeps p q = throwError (ErrTypeMismatchFD p q)

  plusLeq p@(PLeq y z) q@(v, PPlus x' y' z')
    | y == y' && z == z' = return (Just (VPlusR (VVar v)))
    | y == x' && z == z' = return (Just (VPlusL (VVar v)))
  plusLeq _ _ = return Nothing

  byAssump [] p = return Nothing
  byAssump ((v, ap) : as) p =
    do a <- (v,) <$> flattenP ap
       match p a <|>
         plusLeq p a <|>
         byAssump as p

  force p t u =
    do q <- unify t u
       case flattenQ <$> q of
         Just QRefl -> return ()
         _ -> throwError (ErrTypeMismatchPred p t u)

  prim p@(PLeq (TRow y) (TRow z))
    | Just yd <- mapM label y, Just zd <- mapM label z =
      case sequence [elemIndex e zd | e <- yd] of
        Nothing -> return Nothing
        Just is ->
          do mapM_ (\(i, TLabeled _ t) -> let TLabeled _ u = z !! i in force p t u) (zip is y)
             return (Just (VLeqSimple is))
  prim (PPlus (TRow x) (TRow y) (TRow z))
    | Just xd <- mapM label x, Just yd <- mapM label y, Just zd <- mapM label z =
      case sequence [(Left <$> elemIndex e xd) `mplus` (Right <$> elemIndex e yd) | e <- zd] of
        Nothing -> return Nothing
        Just is ->
          do mapM_ align (zip is z)
             return (Just (VPlusSimple is))
    where align (Left i, TLabeled _ t) = force p t u where TLabeled _ u = x !! i
          align (Right i, TLabeled _ t) = force p t u where TLabeled _ u = y !! i
  prim _ = return Nothing

  funCallsFrom :: [Ty] -> Maybe ([Ty], [Ty], [Ty])
  funCallsFrom z
    | Just ls <- mapM label z
    , Just ts <- mapM labeled z
    , Just (fs, es) <- mapAndUnzipM tyAppFrom ts = return (ls, fs, es)
    | otherwise                                  = Nothing
    where tyAppFrom (TApp f e) = Just (f, e)
          tyAppFrom _          = Nothing

  mapArgApp p@(PLeq (TApp (TMapArg y) t) (TApp (TMapArg z) t')) =
    do force p t t'
       fmap (`VLeqLiftR` t) <$> everything (PLeq y z)
  mapArgApp p@(PLeq (TRow []) (TApp (TMapArg z) t)) =
    fmap (`VLeqLiftR` t) <$> everything (PLeq (TRow []) z)
  mapArgApp p@(PLeq (TRow y) (TApp (TMapArg z) t))
    | Just (ls, fs, ts) <- funCallsFrom y =
      do mapM_ (force p t) ts
         fmap (`VLeqLiftR` t) <$> everything (PLeq (TRow (zipWith TLabeled ls fs)) z)
  mapArgApp p@(PLeq (TApp (TMapArg y) t) (TRow [])) =
    fmap (`VLeqLiftR` t) <$> everything (PLeq y (TRow []))
  mapArgApp p@(PLeq (TApp (TMapArg y) t) (TRow z))
    | Just (ls, fs, ts) <- funCallsFrom z =
      do mapM_ (force p t) ts
         fmap (`VLeqLiftR` t) <$> everything (PLeq y (TRow (zipWith TLabeled ls ts)))
  mapArgApp p@(PPlus (TApp (TMapArg x) t) (TApp (TMapArg y) u) (TApp (TMapArg z) v)) =
    do force p t u
       force p u v
       fmap (`VPlusLiftR` t) <$> everything (PPlus x y z)
  mapArgApp _ = return Nothing

  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TApp (TMapFun f') z)) =
    do force p f f'
       fmap (VLeqLiftL f) <$> everything (PLeq y z)
  mapFunApp p@(PLeq (TRow []) (TApp (TMapFun f) z)) =
    fmap (VLeqLiftL f) <$> everything (PLeq (TRow []) z)
  mapFunApp p@(PLeq (TRow y) (TApp (TMapFun f) z))
    | Just (ls, fs, es) <- funCallsFrom y =
      do mapM_ (force p f) fs
         fmap (VLeqLiftL f) <$> everything (PLeq (TRow (zipWith TLabeled ls es)) z)
    | TLam v k (TVar w _) <- f
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel y =
      fmap (VPredEq (QLeq (QMapFun `QTrans` QRow [ QSym (QBeta v k (TVar v (Just k)) t t) | t <- ts]) QRefl) .
            VLeqLiftL f) <$> everything (PLeq (TRow y) z)
  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TRow [])) =
    fmap (VLeqLiftL f) <$> everything (PLeq y (TRow []))
  mapFunApp p@(PLeq (TApp (TMapFun f) y) (TRow z))
    | Just (ls, fs, es) <- funCallsFrom z =
      do mapM_ (force p f) fs
         fmap (VLeqLiftL f) <$> everything (PLeq y (TRow (zipWith TLabeled ls es)))         
    | TLam v k (TVar w _) <- f
    , v == w
    , Just (ls, ts) <- mapAndUnzipM splitLabel z =
      fmap (VPredEq (QLeq QRefl (QMapFun `QTrans` QRow [ QSym (QBeta v k (TVar v (Just k)) t t) | t <- ts])) .
            VLeqLiftL f) <$> everything (PLeq y (TRow z))
  mapFunApp p@(PPlus (TApp (TMapFun f) x) (TApp (TMapFun g) y) (TApp (TMapFun h) z)) =
    do force p f g
       force p g h
       fmap (VPlusLiftL f) <$> everything (PPlus x y z)
  mapFunApp _ = return Nothing


loop :: [Problem] -> CheckM ()
loop [] = return ()
loop ps =
  do (b, ps') <- once False [] ps
     if b
     then loop ps'
     else throwError . ErrNotEntailed =<< mapM notEntailed ps'
  where once b qs [] = return (b, qs)
        once b qs (p : ps) =
          do b' <- solve p
             once (b || b')
                  (if b' then qs else p : qs)
                  ps
        notEntailed (cin, p, _) = 
          do p' <- flattenP p
             ps' <- mapM flattenP [p | (_, p) <- pctxt cin]
             return (p', ps')

andSolve :: CheckM a -> CheckM a
andSolve m =
  censor (const (COut [])) $
  do (x, COut goals) <- listen m
     loop goals
     return x
