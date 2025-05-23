module Checker.Types where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Data.IORef
import Data.List

import Checker.Monad hiding (trace)
import Syntax

trace :: MonadIO m => String -> m ()
trace s = liftIO $
  do b <- readIORef traceKindInference
     when b $ putStrLn s

kindGoal :: String -> CheckM Kind
kindGoal s =
  do kr <- newRef Nothing
     return (KUnif (Goal (s, kr)))

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
  do trace $ show k ++ " ~ " ++ show l
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
unifyK' (KUnif (Goal (uvar, r))) expected =
  do trace $ "binding " ++ show uvar ++ " +-> " ++ show expected
     writeRef r (Just expected)
     return (Just 0)
unifyK' actual (KUnif (Goal (uvar, r))) =
  do trace $ "binding " ++ show uvar ++ " +-> " ++ show actual
     writeRef r (Just actual)
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
     throwError (ErrKindMismatch t actual' expected')

checkTy' :: Term -> Ty -> Kind -> CheckM Ty
checkTy' e t k = withError (ErrContextTerm e . ErrContextType t) $ checkTy t k

checkTy :: Ty -> Kind -> CheckM Ty
checkTy (TVar (-1) x) expected =
  throwError (ErrOther $ "scoping error: " ++ x ++ " not resolved")
checkTy (TVar i v) expected =
  do k <- asks (kbKind . (!! i) . kctxt)
     expectK (TVar i v) k expected
checkTy t@(TUnif (UV {uvKind = k})) expected = expectK t k expected
checkTy TFun expected = expectK TFun (KFun KType (KFun KType KType)) expected
checkTy (TThen pi t) expected =
  TThen <$>
    checkPred pi <*>
    (assume pi $ checkTy t expected)
checkTy (TForall x Nothing t) expected =
  do k <- kindGoal "d"
     checkTy (TForall x (Just k) t) expected
checkTy (TForall x (Just k) t) expected =
  TForall x (Just k) <$> bindTy k (checkTy t expected)
checkTy t@(TLam x Nothing u) expected =
  do k <- kindGoal "d"
     checkTy (TLam x (Just k) u) expected
checkTy t@(TLam x (Just k) u) expected =
  do k' <- kindGoal "cod"
     expectK t (KFun k k') expected
     TLam x (Just k) <$> bindTy k (checkTy u k')
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
     k <- kindGoal "k"
     TSing <$> checkTy l k
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
       Nothing -> fail "explicit rows must be built from concretely labeled types"
       Just ls | nub ls /= ls -> fail "explicit row labels must be unique"
               | otherwise -> return ()
     TRow <$> mapM (\(TLabeled l u) -> TLabeled l <$> checkTy u kelem) ts
  where label (TLabeled (TLab s) _) = Just s
        label _                     = Nothing
checkTy (TPi r) expected = TPi <$> checkTy r (KRow expected)
checkTy (TSigma r) expected = TSigma <$> checkTy r (KRow expected)
checkTy (TMu f) expected = TMu <$> checkTy f (KFun expected expected)
checkTy (TInst ig t) expected =
  TInst ig <$> checkTy t expected
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
checkTy t@(TCompl r0 r1) expected =
  do k <- kindGoal "t"
     expectK t (KRow k) expected
     r0' <- checkTy r0 (KRow k)
     r1' <- checkTy r1 (KRow k)
     v <- newRef Nothing
     require (PLeq r1' r0') v
     return (TCompl r0' r1')

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