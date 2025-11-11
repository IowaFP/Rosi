module Checker (runCheckM, runCheckM', checkTy, checkTop, normalize, TCtxt(..), traceKindInference, traceTypeInference, KBinding(..), typeErrorContext) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Checker.Monad
import Checker.Normalize
import Checker.Preds
import Checker.Terms
import Checker.Types
import Checker.Unify

-- for testing
import Data.IORef
import Syntax

runCheckM m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') emptyTCIn) emptyTCSt) where
  CM m' = andSolve m

runCheckM' d g m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (emptyTCIn { kctxt = d, tctxt = g })) emptyTCSt) where
  CM m' = andSolve m