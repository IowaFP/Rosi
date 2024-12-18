{-# LANGUAGE GeneralisedNewtypeDeriving #-}
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

{-# NOINLINE traceTypeInference #-}
traceTypeInference :: IORef Bool
traceTypeInference = unsafePerformIO (newIORef False)

trace :: MonadIO m => String -> m ()
trace s = liftIO $ 
  do b <- readIORef traceTypeInference
     when b $ putStrLn s

readRef :: MonadIO m => IORef a -> m a
readRef = liftIO . readIORef

writeRef :: MonadIO m => IORef a -> a -> m ()
writeRef x = liftIO . writeIORef x

newRef :: MonadIO m => a -> m (IORef a)
newRef = liftIO . newIORef

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

newtype CSt = CSt { next :: Int }
data CIn = CIn { kctxt :: KCtxt, tctxt :: TCtxt, pctxt :: PCtxt }
type Problem = (CIn, Pred, IORef (Maybe Evid))
newtype COut = COut { goals :: [Problem] }
  deriving (Semigroup, Monoid)

newtype CheckM a = CM (WriterT COut (ReaderT CIn (StateT CSt (ExceptT Error IO))) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader CIn, MonadState CSt, MonadWriter COut, MonadError Error)

instance MonadFail CheckM where
  fail s = throwError (ErrOther s)
  
bindTy :: Kind -> CheckM a -> CheckM a
bindTy k = local (\env -> env { kctxt = (k, Nothing) : kctxt env, tctxt = shiftE (tctxt env), pctxt = map (shiftPN 0 1) (pctxt env)  })

defineTy :: Kind -> Ty -> CheckM a -> CheckM a
defineTy k t = local (\env -> env { kctxt = (k, Just t) : kctxt env, tctxt = shiftE (tctxt env) })

-- Exclusively (so far) for kind checking `TShift t`
unbindTy :: CheckM a -> CheckM a
unbindTy = local (\env -> env { kctxt = tail (kctxt env) })

bind :: Ty -> CheckM a -> CheckM a
bind t = local (\env -> env { tctxt = t : tctxt env })

assume :: Pred -> CheckM a -> CheckM a
assume g = local (\env -> env { pctxt = g : pctxt env })

require :: Pred -> IORef (Maybe Evid) -> CheckM ()
require p r =
  do cin <- ask
     p' <- flattenP p
     trace ("requiring " ++ show p') -- show (pushShiftsP p))
     tell (COut [(cin, p, r)])-- pushShiftsP p, r)])

fresh :: String -> CheckM String
fresh x = do i <- gets next
             modify (\st -> st { next = i + 1 })
             return (x ++ '#' : show i)