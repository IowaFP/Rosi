{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fmap" #-}

module Checker.Monad where

import Control.Monad (foldM, liftM, liftM2, liftM3, mapAndUnzipM, mplus, replicateM, unless, when, zipWithM)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Dynamic
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

traceM :: MonadIO m => m String -> m ()
traceM ms =
  do b <- liftIO $ readIORef traceTypeInference
     when b (ms >>= liftIO . putStrLn)

class Monad m => MonadRef m where
  readRef :: IORef a -> m a
  writeRef :: Typeable a => IORef a -> a -> m ()
  newRef :: Typeable a => a -> m (IORef a)

data KBinding =
    KBVar { kbKind :: Kind, kbLevel :: Int }
  | KBDefn { kbKind :: Kind, kbDefn :: Ty }
  deriving (Eq, Show)

type KCtxt = [KBinding]
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

emptyTCSt :: TCSt
emptyTCSt = TCSt 0

data TCIn = TCIn { kctxt :: KCtxt, tctxt :: TCtxt, pctxt :: PCtxt, level :: Int, ectxt :: Error -> Error }

emptyTCIn :: TCIn
emptyTCIn = TCIn [] [] [] 0 id

type Problem = (TCIn, Pred, IORef (Maybe Evid))
newtype TCOut = TCOut { goals :: [Problem] }
  deriving (Semigroup, Monoid)

newtype CheckM a = CM (WriterT TCOut (ReaderT TCIn (StateT TCSt (ExceptT Error IO))) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader TCIn, MonadState TCSt, MonadWriter TCOut)

instance MonadError Error CheckM where
  throwError e = do f <- asks ectxt
                    CM (throwError (f e))

  catchError e k = CM (catchError (unCM e) (\e -> unCM (k e)))
    where unCM (CM m) = m

instance MonadFail CheckM where
  fail s = throwError (ErrOther s)

instance MonadRef CheckM where
  newRef = liftIO . newIORef
  readRef = liftIO . readIORef
  writeRef r = liftIO . writeIORef r

class (Monad m, MonadFail m, MonadRef m, MonadIO m, MonadReader TCIn m) => MonadCheck m where
  bindTy :: Kind -> m a -> m a
  bindTy k = local (\env -> env { kctxt = KBVar k (level env) : kctxt env, tctxt = shiftE (tctxt env), pctxt = map (shiftPNV [] 0 1) (pctxt env) })

  defineTy :: Kind -> Ty -> m a -> m a
  defineTy k t = local (\env -> env { kctxt = KBDefn k t : kctxt env, tctxt = shiftE (tctxt env), level = level env + 1 })

  bind :: Ty -> m a -> m a
  bind t = local (\env -> env { tctxt = t : tctxt env })

  assume :: Pred -> m a -> m a
  assume g = local (\env -> env { pctxt = g : pctxt env })

  require :: Pred -> IORef (Maybe Evid) -> m ()

  typeError :: Error -> m a

  typeErrorContext :: (Error -> Error) -> m a -> m a
  typeErrorContext f = local (\env -> env { ectxt = ectxt env . f})

  fresh :: String -> m String

  atLevel :: Int -> m t -> m t
  atLevel l = local (\st -> st { level = l })

  theLevel :: m Int
  theLevel = asks level

instance MonadCheck CheckM where
  require p r =
    do cin <- ask
       p' <- flattenP p
       trace ("requiring " ++ show p')
       tell (TCOut [(cin, p, r)])

  typeError = throwError

  fresh x = do i <- gets next
               modify (\st -> st { next = i + 1 })
               return ((takeWhile ('#' /=) x) ++ '#' : show i)


collect :: CheckM a -> CheckM (a, TCOut)
collect m = censor (const (TCOut [])) $ listen m

upLevel m = do l <- theLevel
               atLevel (l + 1) m

--


data Update where
  U :: IORef a -> a -> Update

perform :: MonadIO m => Update -> m ()
perform (U ref val) = liftIO $ writeIORef ref val

type Eqn = (Ty, (Ty, Evid))

type UR = [Eqn]
type US = Maybe [Dynamic]
type UW = ([Update], [(TCIn, Pred, IORef (Maybe Evid))])
newtype UnifyM a = UM { runUnifyM :: ExceptT (Ty, Ty) (StateT US (WriterT UW (ReaderT UR CheckM))) a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadWriter UW, MonadIO, MonadState US)

instance MonadRef UnifyM where
  newRef v = UM $ ExceptT $ StateT $ \checking -> WriterT (body checking) where
    body Nothing = do r <- liftIO (newIORef v)
                      return ((Right r, Nothing), ([], []))
    body (Just rs) = do r <- liftIO (newIORef v)
                        return ((Right r, Just (toDyn r : rs)), ([], []))
  readRef = liftIO . readIORef
  writeRef r v =
    do v' <- readRef r
       tell ([U r v'], [])
       liftIO (writeIORef r v)

instance MonadReader TCIn UnifyM where
  ask = UM (lift (lift (lift (lift ask))))
  local f r = UM $ ExceptT $ StateT $ \checking -> WriterT $ (ReaderT $ \eqns -> local f (runReaderT (runWriterT (runStateT (runExceptT (runUnifyM r)) checking)) eqns))

instance MonadCheck UnifyM where
  require p r =
    do cin <- ask
       tell ([], [(cin, p, r)])

  typeError e = UM (lift (lift (lift (lift (typeError e)))))

  fresh = UM . lift . lift . lift . lift . fresh

canUpdate :: Typeable a => IORef a -> UnifyM Bool
canUpdate r = UM (ExceptT $ StateT $ \checking -> WriterT (body checking)) where
  body Nothing = return ((Right True, Nothing), ([], []))
  body (Just rs) = return ((Right (any ok rs), Just rs), ([], []))
  ok dr = case fromDynamic dr of
            Just r' -> r == r'
            Nothing -> False

theEqns :: UnifyM [Eqn]
theEqns = UM ask

unificationFails :: Ty -> Ty -> UnifyM a
unificationFails actual expected = UM (throwError (actual, expected))

try :: UnifyM a -> UnifyM (Maybe a)
try (UM body) =
  UM $ either (const Nothing) Just <$> tryError body

bracket :: UnifyM () -> UnifyM a -> UnifyM () -> UnifyM a
bracket (UM before) (UM body) (UM after) =
  UM $ do before
          z <- body `catchError` (\e -> do after; throwError e)
          after
          return z
