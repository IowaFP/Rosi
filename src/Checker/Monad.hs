{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fmap" #-}

module Checker.Monad where

import Control.Monad (foldM, liftM, liftM2, liftM3, mapAndUnzipM, mplus, replicateM, unless, when, zipWithM)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Data
import Data.IORef
import Data.List (elemIndex, nub)
import GHC.Stack
import System.IO.Unsafe (unsafePerformIO)

import Syntax

{-# NOINLINE traceKindInference #-}
traceKindInference :: IORef Bool
traceKindInference = unsafePerformIO (newIORef False)

{-# NOINLINE traceTypeInference #-}
traceTypeInference :: IORef Bool
traceTypeInference = unsafePerformIO (newIORef False)

trace :: MonadIO m => String -> m ()
trace s = liftIO $
  do b <- readIORef traceTypeInference
     when b $ putStrLn s

class Monad m => MonadRef m where
  readRef :: IORef a -> m a
  writeRef :: Typeable a => IORef a -> a -> m ()
  newRef :: Typeable a => a -> m (IORef a)

type KCtxt = [(Kind, Maybe Ty)]
-- capturing type *definitions* in the kinding context as well; quantifier- and
-- lambda-bound type definitions get a `Nothing` in the second component.
-- data TCtxt = Emp | Shift TCtxt | Bind Ty TCtxt
--   deriving (Data, Eq, Show, Typeable)
type TCtxt = [Ty]
type PCtxt = [Pred]

lookupV :: HasCallStack => Int -> TCtxt -> Ty
lookupV _ [] = error "lookupV: index out of range"
lookupV 0 (t : _) = t
lookupV n (_ : ts) = lookupV (n - 1) ts

shiftE :: TCtxt -> TCtxt
shiftE = map (shiftTN 0 1)

newtype TCSt = TCSt { next :: Int }
emptyTCSt = TCSt 0
data TCIn = TCIn { kctxt :: KCtxt, tctxt :: TCtxt, pctxt :: PCtxt, level :: Int }
emptyTCIn = TCIn [] [] [] 0
type Problem = (TCIn, Pred, IORef (Maybe Evid))
newtype TCOut = TCOut { goals :: [Problem] }
  deriving (Semigroup, Monoid)

newtype CheckM a = CM (WriterT TCOut (ReaderT TCIn (StateT TCSt (ExceptT Error IO))) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader TCIn, MonadState TCSt, MonadWriter TCOut, MonadError Error)

instance MonadFail CheckM where
  fail s = throwError (ErrOther s)

instance MonadRef CheckM where
  newRef = liftIO . newIORef
  readRef = liftIO . readIORef
  writeRef r = liftIO . writeIORef r

class (Monad m, MonadFail m, MonadError Error m, MonadRef m, MonadIO m, MonadReader TCIn m) => MonadCheck m where
  bindTy :: Kind -> m a -> m a
  defineTy :: Kind -> Ty -> m a -> m a
  bind :: Ty -> m a -> m a

  assume :: Pred -> m a -> m a
  require :: Pred -> IORef (Maybe Evid) -> m ()

  fresh :: String -> m String
  upLevel :: m a -> m a
  theLevel :: m Int

instance MonadCheck CheckM where
  bindTy k = local (\env -> env { kctxt = (k, Nothing) : kctxt env, tctxt = shiftE (tctxt env), pctxt = map (shiftPNV [] 0 1) (pctxt env)  })
  defineTy k t = local (\env -> env { kctxt = (k, Just t) : kctxt env, tctxt = shiftE (tctxt env) })
  bind t = local (\env -> env { tctxt = t : tctxt env })
  assume g = local (\env -> env { pctxt = g : pctxt env })
  require p r =
    do cin <- ask
       p' <- flattenP p
       trace ("requiring " ++ show p')
       tell (TCOut [(cin, p, r)])
  fresh x = do i <- gets next
               modify (\st -> st { next = i + 1 })
               return ((takeWhile ('#' /=) x) ++ '#' : show i)
  upLevel = local (\st -> st { level = level st + 1 })
  theLevel = asks level