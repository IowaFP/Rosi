{-# LANGUAGE GeneralisedNewtypeDeriving, PatternGuards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fmap" #-}

module Checker.Monad where

import Control.Monad (foldM, liftM, liftM2, liftM3, mapAndUnzipM, mplus, replicateM, unless, when, zipWithM)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.IORef
import Data.List (elemIndex, nub)

import Syntax

trace, trace' :: MonadIO m => String -> m ()
-- trace = liftIO . putStrLn 
trace _ = return ()
trace' = liftIO . putStrLn

readRef :: MonadIO m => IORef a -> m a
readRef = liftIO . readIORef

writeRef :: MonadIO m => IORef a -> a -> m ()
writeRef x = liftIO . writeIORef x

newRef :: MonadIO m => a -> m (IORef a)
newRef = liftIO . newIORef

type KCtxt = [(Kind, Maybe Ty)] 
-- capturing type *definitions* in the kinding context as well; quantifier- and
-- lambda-bound type definitions get a `Nothing` in the second component.
type TCtxt = [Ty]
type PCtxt = [Pred]

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
bindTy k = local (\env -> env { kctxt = (k, Nothing) : kctxt env })

defineTy :: Kind -> Ty -> CheckM a -> CheckM a
defineTy k t = local (\env -> env { kctxt = (k, Just t) : kctxt env })

bind :: Ty -> CheckM a -> CheckM a
bind t = local (\env -> env { tctxt = t : tctxt env })

assume :: Pred -> CheckM a -> CheckM a
assume g = local (\env -> env { pctxt = g : pctxt env })

require :: Pred -> IORef (Maybe Evid) -> CheckM ()
require p r =
  do cin <- ask
     tell (COut [(cin, p, r)])

fresh :: String -> CheckM String
fresh x = do i <- gets next
             modify (\st -> st { next = i + 1 })
             return (x ++ '$' : show i)