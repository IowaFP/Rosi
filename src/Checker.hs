module Checker (runCheckM, runCheckM', checkTy, checkTop) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Checker.Monad
import Checker.Preds
import Checker.Terms
import Checker.Types
import Checker.Unify

runCheckM m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (CIn [] [] [])) (CSt 0)) where
  CM m' = andSolve m

runCheckM' g m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (CIn [] g [])) (CSt 0)) where
  CM m' = andSolve m
