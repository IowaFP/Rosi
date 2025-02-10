module Checker (runCheckM, runCheckM', checkTy, checkTop, normalize, TCtxt(..), traceTypeInference) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Checker.Monad
import Checker.Preds
import Checker.Terms
import Checker.Types
import Checker.Unify

runCheckM m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (TCIn [] [] [])) (TCSt 0)) where
  CM m' = andSolve m

runCheckM' d g m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (TCIn d g [])) (TCSt 0)) where
  CM m' = andSolve m
