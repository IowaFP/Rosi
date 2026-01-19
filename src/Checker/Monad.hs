{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fmap" #-}

module Checker.Monad where

import Control.Monad (foldM, liftM, liftM2, liftM3, mapAndUnzipM, mplus, replicateM, unless, when, zipWithM)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (second)
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
    KBVar { kbKind :: Kind, kbLevel :: Level }
  | KBDefn { kbKind :: Kind, kbDefn :: Ty }
  deriving (Eq, Show)

type KCtxt = [KBinding]
-- capturing type *definitions* in the kinding context as well; quantifier- and
-- lambda-bound type definitions get a `Nothing` in the second component.
-- data TCtxt = Emp | Shift TCtxt | Bind Ty TCtxt
--   deriving (Data, Eq, Show, Typeable)
type TCtxt = [(QName, Ty)]
type PCtxt = [Pred]

lookupV :: HasCallStack => Int -> TCtxt -> Ty
lookupV _ [] = error "lookupV: index out of range"
lookupV 0 ((_, t) : _) = t
lookupV n (_ : ts)     = lookupV (n - 1) ts

shiftE :: TCtxt -> TCtxt
shiftE = map (second (shiftTN 0 1))

data Update where
  U :: IORef a -> a -> Update

data Mark = Mark Int
  deriving Eq

perform :: MonadIO m => Update -> m ()
perform (U ref val) = liftIO $ writeIORef ref val

data TCSt = TCSt { updates :: [(Mark, [Update])], next :: Int }

pushUpdate :: IORef a -> a -> TCSt -> TCSt
pushUpdate v x st
  | [] <- updates st = st
  | (m, us) : rest <- updates st = st { updates = (m, U v x : us) : rest}

emptyTCSt :: TCSt
emptyTCSt = TCSt [] 0

data TCIn = TCIn { kctxt :: KCtxt, tctxt :: TCtxt, pctxt :: PCtxt, level :: Level, ectxt :: Error -> Error }

emptyTCIn :: TCIn
emptyTCIn = TCIn [] [] [] 0 id

type Problem = (TCIn, Pred, IORef (Maybe Evid))
data TCOut = TCOut { goals :: [Problem], holes :: [(String, Ty, TCIn)] }

instance Semigroup TCOut where
  TCOut goals holes <> TCOut goals' holes' = TCOut (goals <> goals') (holes <> holes')

instance Monoid TCOut where
  mempty = TCOut mempty mempty

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
  writeRef r new =
    do old <- liftIO (readIORef r)
       modify (pushUpdate r old)
       liftIO (writeIORef r new)

class (Monad m, MonadFail m, MonadRef m, MonadIO m, MonadReader TCIn m) => MonadCheck m where
  bindTy :: Kind -> m a -> m a
  bindTy k = local (\env -> env { kctxt = KBVar k (level env) : kctxt env, tctxt = shiftE (tctxt env), pctxt = map (shiftPNV [] 0 1) (pctxt env) })

  defineTy :: Kind -> Ty -> m a -> m a
  defineTy k t = local (\env -> env { kctxt = KBDefn k t : kctxt env, tctxt = shiftE (tctxt env), level = level env + 1 })

  bind :: String -> Ty -> m a -> m a
  bind x t = local (\env -> env { tctxt = ([x, ""], t) : tctxt env })  -- assuming that we only call `bind` with local variables

  assume :: Pred -> m a -> m a
  assume g = local (\env -> env { pctxt = g : pctxt env })

  require :: Pred -> IORef (Maybe Evid) -> m ()

  typeError :: Error -> m a

  typeErrorContext :: (Error -> Error) -> m a -> m a
  typeErrorContext f = local (\env -> env { ectxt = ectxt env . f})

  fresh :: String -> m String

  atLevel :: Level -> m t -> m t
  atLevel l = local (\st -> st { level = l })

  theLevel :: m Level
  theLevel = asks level

  mark :: m Mark
  reset :: Mark -> m ()

instance MonadCheck CheckM where
  require p r =
    do cin <- ask
       p' <- flattenP p
       trace ("requiring " ++ show p')
       tell (TCOut [(cin, p, r)] [])

  typeError = throwError

  fresh x = do i <- gets next
               modify (\st -> st { next = i + 1 })
               return ((takeWhile ('#' /=) x) ++ '#' : show i)

  mark = do st <- get
            let m = Mark (next st)
            put (st { updates = (m, []) : updates st, next = next st + 1})
            return m

  reset m = gets updates >>= resetLoop where
    resetLoop [] =
      do modify (\st -> st { updates = [] })
         return ()
    resetLoop ((m', us) : rest) =
      do mapM_ perform us
         when (m /= m') $ resetLoop rest

collect :: CheckM a -> CheckM (a, [Problem])
collect m = censor (\out -> out { goals = [] }) $ (second goals <$> listen m)

upLevel m = do l <- theLevel
               atLevel (l + 1) m

--

type Eqn = (Ty, (Ty, Evid))

type UR = [Eqn]
type US = Maybe [Dynamic]
type UW = [(TCIn, Pred, IORef (Maybe Evid))]
newtype UnifyM a = UM { runUnifyM :: ExceptT (Ty, Ty) (StateT US (WriterT UW (ReaderT UR CheckM))) a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadWriter UW, MonadIO, MonadState US)

liftToUnifyM :: CheckM a -> UnifyM a
liftToUnifyM = UM . lift . lift . lift . lift


instance MonadRef UnifyM where
  newRef v = UM $ ExceptT $ StateT $ \checking -> WriterT (body checking) where
    body Nothing = do r <- lift (newRef v)
                      return ((Right r, Nothing), [])
    body (Just rs) = do r <- lift (newRef v)
                        return ((Right r, Just (toDyn r : rs)), [])
  readRef = liftToUnifyM . readRef
  writeRef r v = liftToUnifyM (writeRef r v)


instance MonadReader TCIn UnifyM where
  ask = liftToUnifyM ask
  local f r = UM $ ExceptT $ StateT $ \checking -> WriterT $ (ReaderT $ \eqns -> local f (runReaderT (runWriterT (runStateT (runExceptT (runUnifyM r)) checking)) eqns))

instance MonadCheck UnifyM where
  require p r =
    do cin <- ask
       tell [(cin, p, r)]

  mark = liftToUnifyM mark

  reset = liftToUnifyM . reset

  typeError = liftToUnifyM . typeError

  fresh = liftToUnifyM . fresh

canUpdate :: Typeable a => IORef a -> UnifyM Bool
canUpdate r = UM (ExceptT $ StateT $ \checking -> WriterT (body checking)) where
  body Nothing = return ((Right True, Nothing), [])
  body (Just rs) = return ((Right (any ok rs), Just rs), [])
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

-- testing code

