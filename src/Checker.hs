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

-- for testing
import Data.IORef
import Syntax

runCheckM m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (TCIn [] [] [])) (TCSt 0)) where
  CM m' = andSolve m

runCheckM' d g m = runExceptT (fst <$> evalStateT (runReaderT (runWriterT m') (TCIn d g [])) (TCSt 0)) where
  CM m' = andSolve m

{-
Puzzle idea:

  f {} ~ Sigma r
  f ~ \x. Sigma x

Should succeed, learning

  f +-> \x. Sigma x
  r +-> {}
-}

puzzle :: CheckM (IORef (Maybe Ty), IORef (Maybe Ty), IORef (Maybe Evid), IORef (Maybe Evid))
puzzle =
  andSolve $
  do f <- newRef Nothing
     r <- newRef Nothing
     v1 <- newRef Nothing
     v2 <- newRef Nothing
     let gf = Goal ("f", f)
         rf = Goal ("r", r)
         q1 = Goal ( "q1", v1)
         q2 = Goal ( "q2", v2)
         t1 = TApp (TUnif 0 gf (KFun KType KType)) (TRow [])
         u1 = TSigma (TUnif 0 rf (KRow KType))
         t2 = TUnif 0 gf (KFun KType KType)
         u2 = TLam "x" (Just KType) (TSigma (TVar 0 "x" (Just (KRow KType))))
     require (PEq t1 u1) v1
     require (PEq t2 u2) v2
     return (f, r, v1, v2)

-- but this puzzle should now succeed, because unification tries to delay equalities
puzzle2 :: CheckM (IORef (Maybe Ty), IORef (Maybe Ty), Maybe Evid, Maybe Evid)
puzzle2 =
  andSolve $
  do f <- newRef Nothing
     r <- newRef Nothing
     -- v1 <- newRef Nothing
     -- v2 <- newRef Nothing
     let gf = Goal ("f", f)
         rf = Goal ("r", r)
         -- q1 = Goal ( "q1", v1)
         -- q2 = Goal ( "q2", v2)
         t1 = TApp (TUnif 0 gf (KFun KType KType)) (TRow [])
         u1 = TSigma (TUnif 0 rf (KRow KType))
         t2 = TUnif 0 gf (KFun KType KType)
         u2 = TLam "x" (Just KType) (TSigma (TVar 0 "x" (Just (KRow KType))))
     v1 <- unify [] t1 u1
     v2 <- unify [] t2 u2
     return (f, r, v1, v2)
