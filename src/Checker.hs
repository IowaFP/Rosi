module Checker (runCheckM, runCheckM', checkTy, checkTop, normalize, TCtxt(..), traceKindInference, traceTypeInference, KBinding(..), typeErrorContext) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (second)

import Checker.Monad
import Checker.Normalize
import Checker.Preds
import Checker.Terms
import Checker.Types

import Syntax

third f (a, b, c) = (a, b, f c)

runCheckM :: CheckM a -> IO (Either Error (a, [(String, Ty, TCtxt)]))
runCheckM m = runExceptT (second (map (third tctxt) . holes) <$> evalStateT (runReaderT (runWriterT m') emptyTCIn) emptyTCSt) where
  CM m' = andSolve m

runCheckM' :: KCtxt -> TCtxt -> CheckM a -> IO (Either Error (a, [(String, Ty, TCtxt)]))
runCheckM' d g m = runExceptT (second (map (third tctxt) . holes) <$> evalStateT (runReaderT (runWriterT m') (emptyTCIn { kctxt = d, tctxt = g })) emptyTCSt) where
  CM m' = andSolve m