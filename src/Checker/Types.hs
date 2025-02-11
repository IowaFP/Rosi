module Checker.Types where

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Data.List

import Checker.Monad
import Syntax

kindGoal :: String -> CheckM Kind
kindGoal s =
  do kr <- newRef Nothing
     return (KUnif (Goal ("k$" ++ s, kr)))

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

kindMismatch :: MonadCheck m => Ty -> Kind -> Kind -> m a
kindMismatch t actual expected =
  do actual' <- flattenK actual
     expected' <- flattenK expected
     throwError (ErrKindMismatch t actual' expected')

checkTy' :: Term -> Ty -> Kind -> CheckM Ty
checkTy' e t k = withError (ErrContextTerm e . ErrContextType t) $ checkTy t k

checkTy :: Ty -> Kind -> CheckM Ty
checkTy (TVar (-1) x _) expected =
  throwError (ErrOther $ "scoping error: " ++ x ++ " not resolved")
checkTy (TVar i v Nothing) expected =
  do (k, _) <- asks ((!! i) . kctxt)
     expectK (TVar i v (Just k)) k expected
checkTy (TVar i v (Just kv)) expected =
  do (k, _) <- asks ((!! i) . kctxt)
     expectK (TVar i v (Just k)) kv k
     expectK (TVar i v (Just k)) k expected
checkTy t@(TUnif _ _ k) expected = expectK t k expected
checkTy TFun expected = expectK TFun (KFun KType (KFun KType KType)) expected
checkTy (TThen pi t) expected =
  TThen <$>
    checkPred pi <*>
    checkTy t expected
checkTy (TForall x k t) expected =
  TForall x k <$> bindTy k (checkTy t expected)
checkTy t@(TLam x k u) expected =
  do k' <- kindGoal "d"
     expectK t (KFun k k') expected
     TLam x k <$> bindTy k (checkTy u k')
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
       Nothing -> fail "explicit rows must be built from explicitly labeled types"
       Just ls | nub ls /= ls -> fail "explicit row labels must be unique"
               | otherwise -> return ()
     TRow <$> mapM (\(TLabeled l u) -> TLabeled l <$> checkTy u kelem) ts
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