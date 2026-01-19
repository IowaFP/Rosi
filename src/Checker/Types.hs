module Checker.Types where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer
import Data.IORef
import Data.List

import Checker.Monad hiding (collect, trace)
import Checker.Normalize
import Checker.Utils
import Printer
import Syntax

trace :: MonadIO m => String -> m ()
trace s = liftIO $
  do b <- readIORef traceKindInference
     when b $ putStrLn s

bindRef :: MonadCheck m => Goal Kind -> Maybe Kind -> m ()
bindRef (Goal (_, r)) Nothing =
  writeRef r Nothing
bindRef (Goal (s, r)) (Just k) =
  do b <- check k
     if b
     then writeRef r (Just k)
     else error $ "rejecting binding " ++ s ++ " +-> " ++ renderString (ppr k)
  where check KType = return True
        check KLabel = return True
        check (KRow k) = check k
        check (KFun k1 k2) = (&&) <$> check k1 <*> check k2
        check (KUnif (Goal (_, r')))
          | r == r' = return False
          | otherwise = do k' <- readRef r'
                           case k' of
                             Just k'' -> check k''
                             Nothing -> return True

  -- Note: just returning a `Ty` here out of convenience; it's always an exactly the input `Ty`.
expectK :: MonadCheck m => Ty -> Kind -> Kind -> m Ty
expectK t actual expected =
  do i <- expectKR t actual expected
     when (i /= 0) $
       kindMismatch t actual expected
     return t

expectKR :: MonadCheck m => Ty -> Kind -> Kind -> m Int
expectKR t actual expected =
  do mi <- unifyK actual expected
     case mi of
       Nothing -> kindMismatch t actual expected
       Just i  -> return i

unifyK :: MonadCheck m => Kind -> Kind -> m (Maybe Int)
unifyK k l =
  do -- trace $ show k ++ " ~ " ++ show l
     k' <- open k
     l' <- open l
     unifyK' k' l'
  where open k@(KUnif (Goal (_, r))) =
          do mk <- readRef r
             case mk of
               Just k' -> open k'
               Nothing -> return k
        open k = return k

unifyK' KType KType = return (Just 0)
unifyK' KLabel KLabel = return (Just 0)
unifyK' (KUnif (Goal (_, r))) (KUnif (Goal (_, s)))
  | r == s = return (Just 0)
unifyK' (KUnif g@(Goal (uvar, r))) expected =
  do trace $ "binding " ++ show uvar ++ " +-> " ++ show expected
     bindRef g (Just expected)
     return (Just 0)
unifyK' actual (KUnif g@(Goal (uvar, r))) =
  do trace $ "binding " ++ show uvar ++ " +-> " ++ show actual
     bindRef g (Just actual)
     return (Just 0)
unifyK' (KRow rActual) (KRow rExpected) = unifyK rActual rExpected
unifyK' (KRow rActual) kExpected = ((1+) <$>) <$> unifyK rActual kExpected
unifyK' (KFun dActual cActual) (KFun dExpected cExpected) =
  (*&*) <$> unifyK dActual dExpected <*> unifyK cActual cExpected where
  Just 0 *&* Just 0 = Just 0
  _ *&* _ = Nothing
unifyK' _ _ =
  return Nothing

kindMismatch :: MonadCheck m => Ty -> Kind -> Kind -> m a
kindMismatch t actual expected =
  do actual' <- flattenK actual
     expected' <- flattenK expected
     typeError (ErrContextType t (ErrKindMismatch actual' expected'))

--

type KCOut = [(Pred, UVar)]
newtype KindM a = K {runKindM :: WriterT KCOut CheckM a}
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadReader TCIn, MonadWriter KCOut)

instance MonadRef KindM where
  newRef = K . lift . newRef
  readRef = K . lift . readRef
  writeRef r = K . lift . writeRef r

instance MonadCheck KindM where
  require p = K . lift . require p
  typeError = K . lift . typeError
  fresh = K . lift . fresh
  mark = K (lift mark)
  reset = K . lift . reset

collect :: KindM a -> KindM (a, KCOut)
collect = censor (const []) . listen

toCheckM :: KindM Ty -> CheckM Ty
toCheckM m =
  do (t, ps) <- runWriterT (runKindM m)
     if null ps
     then return t
     else typeError (ErrTypeDesugaring t)

--

checkTy' :: Term -> Ty -> Kind -> KindM Ty
checkTy' e t k = typeErrorContext (ErrContextTerm e . ErrContextType t) $ checkTy t k

checkTy :: Ty -> Kind -> KindM Ty
checkTy t k =
  do trace $ "checkTy " ++ renderString (ppr t) ++ " : " ++ renderString (ppr k)
     typeErrorContext (ErrContextType t) (checkTy0 t k)

--

implicitConstraints :: Ty -> Kind -> KindM Ty
implicitConstraints t expected =
  do ks' <- mapM (maybe (kindGoal "d") return) ks
     (t2, pairs) <- collect $ foldr bindTy (checkTy t' expected) ks'
     let (here, there) = partition (tvFreeInP [0..length bs - 1] . fst) pairs
         (ps, uvs) = unzip here
         t3 = shiftTNV uvs 0 (length uvs) (foldr TThen t2 ps)
         insts = [(goalRef (uvGoal v), Just (TVar i [s, ""])) | (v, i) <- zip (reverse uvs) [0..], let s = goalName (uvGoal v)]
         t4 = rebind (zip xs (map Just ks') ++ [(x, Just k) | v <- uvs, let x = goalName (uvGoal v), let k = uvKind v]) t3
     tell there
     mapM_ (uncurry writeRef) insts
     return t4
  where (bs, t') = tybinders t
        (xs, ks) = unzip bs

--

checkTy0 :: Ty -> Kind -> KindM Ty
checkTy0 (TVar (-1) x) expected =
  typeError (ErrOther $ "scoping error: " ++ head x ++ " not resolved")
checkTy0 (TVar i v) expected =
  do k <- asks (kbKind . (!! i) . kctxt)
     expectK (TVar i v) k expected
checkTy0 t@(TUnif (UV {uvKind = k})) expected = expectK t k expected
checkTy0 TFun expected = expectK TFun (KFun KType (KFun KType KType)) expected
checkTy0 (TThen pi t) expected =
  TThen <$>
    checkPred pi <*>
    (assume pi $ checkTy t expected)
checkTy0 t@(TForall {}) expected =
  implicitConstraints t expected
checkTy0 t@(TLam x Nothing u) expected =
  do k <- kindGoal "d"
     (t', bs) <- collect $ checkTy (TLam x (Just k) u) expected
     if null bs then return t' else typeError (ErrTypeDesugaring t)
checkTy0 t@(TLam x (Just k) u) expected =
  do k' <- kindGoal "cod"
     expectK t (KFun k k') expected
     (t', bs) <- collect $ TLam x (Just k) <$> bindTy k (checkTy u k')
     if null bs then return t' else typeError (ErrTypeDesugaring t)
checkTy0 (TApp t u) expected =
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
     return (TApp (foldr ($) t' (replicate n TMapApp ++ replicate m TMap)) u')
checkTy0 t@(TLab _) expected = expectK t KLabel expected
checkTy0 t@(TSing l) expected =
  do expectK t KType expected
     k <- kindGoal "k"
     TSing <$> checkTy l k
checkTy0 t@(TLabeled l u) expected =
  TLabeled <$>
    checkTy l KLabel <*>
    checkTy u expected
checkTy0 t@(TRow [TLabeled lt et]) expected =
  do kelem <- kindGoal "e"
     expectK t (KRow kelem) expected
     lt' <- checkTy lt KLabel
     et' <- checkTy et kelem
     return (TRow [TLabeled lt' et'])
checkTy0 t@(TRow ts) expected =
  -- Note, building in our row theory here...
  do kelem <- kindGoal "e"
     expectK t (KRow kelem) expected
     case mapM label ts of
       Nothing -> fail "explicit rows must be built from concretely labeled types"
       Just ls | nub ls /= ls -> fail "explicit row labels must be unique"
               | otherwise -> return ()
     TRow <$> mapM (\(TLabeled l u) -> TLabeled l <$> checkTy u kelem) ts
  where label (TLabeled (TLab s) _) = Just s
        label _                     = Nothing
checkTy0 (TConApp Pi r) expected = TConApp Pi <$> checkTy r (KRow expected)
checkTy0 (TConApp Sigma r) expected = TConApp Sigma <$> checkTy r (KRow expected)
checkTy0 (TConApp (Mu count) f) expected = TConApp (Mu count) <$> checkTy f (KFun expected expected)
checkTy0 (TConApp (TCUnif g) t) expected =
  do mk <- readRef (goalRef g)
     case mk of
       Just k -> checkTy0 (TConApp k t) expected
       Nothing -> fail "don't know how to kind check unknown constructor application"
checkTy0 (TInst ig t) expected =
  TInst ig <$> checkTy t expected
checkTy0 t@(TMap f) expected =
  do kdom <- kindGoal "d"
     kcod <- kindGoal "c"
     expectK t (KFun (KRow kdom) (KRow kcod)) expected
     TMap <$> checkTy f (KFun kdom kcod)
checkTy0 t@(TMapApp f) expected =
  do kdom <- kindGoal "d"
     kcod <- kindGoal "e"
     expectK t (KFun kcod (KRow kcod)) expected
     TMap <$> checkTy f (KFun kdom kcod)
checkTy0 t@(TCompl r0 r1) expected =
  do k <- kindGoal "t"
     expectK t (KRow k) expected
     r0' <- checkTy r0 (KRow k)
     r1' <- checkTy r1 (KRow k)
     v <- newRef Nothing
     require (PLeq r1' r0') v
     return (TCompl r0' r1')
checkTy0 TString expected =
  expectK TString KType expected
checkTy0 t@(TPlus x y) expected =
  do k <- kindGoal "e"
     expectK t (KRow k) expected
     x' <- (fst <$>) . normalize [] =<< checkTy x (KRow k)
     y' <- (fst <$>) . normalize [] =<< checkTy y (KRow k)
     case (x', y') of
       (TRow xr, TRow yr)
         | Just xs <- mapM splitConcrete xr, Just ys <- mapM splitConcrete yr ->
           if any (`elem` xs) ys
           then typeError (ErrTypeDesugaring t)
           else return (TRow (map (uncurry TLabeled) (xs ++ ys)))
       _ -> do z@(TUnif v) <- typeGoal' "z" (KRow k)
               tell [(PPlus x' y' z, v)]
               return z
    where splitConcrete (TLabeled (TLab s) x) = Just (TLab s, x)
          splitConcrete _ = Nothing
checkTy0 t@(TConOrd k rel u) expected =
  do u' <- checkTy u (KRow expected)
     z@(TUnif v) <- typeGoal' "z" (KRow expected)
     tell [(case rel of
              Leq -> PLeq z u'
              Geq -> PLeq u' z, v)]
     return (TConApp k z)

checkPred :: Pred -> KindM Pred
checkPred p@(PLeq y z) =
  typeErrorContext (ErrContextPred p)  $
  do kelem <- kindGoal "e"
     PLeq <$> checkTy y (KRow kelem)
          <*> checkTy z (KRow kelem)
checkPred p@(PPlus x y z) =
  typeErrorContext (ErrContextPred p) $
  do kelem <- kindGoal "e"
     PPlus <$> checkTy x (KRow kelem)
           <*> checkTy y (KRow kelem)
           <*> checkTy z (KRow kelem)
checkPred p@(PEq t u) =
  typeErrorContext (ErrContextPred p) $
  do k <- kindGoal "k"
     PEq <$> checkTy t k
         <*> checkTy u k
checkPred p@(PFold z) =
  typeErrorContext (ErrContextPred p) $
  do kelem <- kindGoal "e"
     PFold <$> checkTy z (KRow kelem)