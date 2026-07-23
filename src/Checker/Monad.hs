{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- HLINT ignore "Use fmap" -}

module Checker.Monad where

import Control.Monad        (when)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor       (second)
import Data.Dynamic
import Data.IORef
import GHC.Stack
import System.IO.Unsafe     (unsafePerformIO)

import Data.Typeable        (cast)
import Errors
import Printer              hiding (level)
import Syntax

-- ==============================================================================
-- Tracing
-- ==============================================================================

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

-- -----------------------------------------------------------------------------
-- Pseudotypes
--
-- We might prefer that pseudotypes (just `TInst` for now, although there will
-- hopefully be a corresponding thing for generalization in the future) stay out
-- of the context. The intuition here is that it's not clear what it means to
-- have an assumption `x : [Int]Int->Int`... does this mean `x : forall a. a ->
-- a`? `x : forall a. a -> Int`? We can't have both possibilities...
--
-- Unfortunately, it turns out that pseudotypes do regularly show up in the
-- context, as was demonstrated using the following functions.  The current
-- solution to the above problem is to be careful about how such an assumption
-- is refine in the future. Nevertheless, I'm leaving these here in case this
-- approach is rethought.
-- -----------------------------------------------------------------------------

checkXType :: MonadIO m => Ty -> m ()
checkXType t =
  liftIO $ do b <- readIORef traceTypeInference
              when b $
                do x <- isXType t
                   when x $ trace $ "binding x-type: " ++ renderString (ppr t)

checkXPred :: MonadIO m => String -> Pred -> m ()
checkXPred s p =
  liftIO $ do b <- readIORef traceTypeInference
              when b $
                do x <- isXPred p
                   when x $ trace $ s ++ " x-pred: " ++ renderString (ppr p)

(<||>) :: Applicative m => m Bool -> m Bool -> m Bool
(<||>) = liftA2 (||)

isXType :: MonadIO m => Ty -> m Bool
isXType (TVar {})       = return False
isXType (TUnif uv)      = maybe (return False) isXType =<< liftIO (readIORef (goalRef (uvGoal uv)))
isXType TFun            = return False
isXType (TForall _ _ t) = isXType t
isXType (TThen p t)     = isXPred p <||> isXType t
isXType (TExists _ _ t) = isXType t
isXType (TExistsP p t)  = isXPred p <||> isXType t
isXType (TLam _ _ t)    = isXType t
isXType (TApp t u)      = isXType t <||> isXType u
isXType (TLab {})       = return False
isXType (TSing t)       = isXType t
isXType (TLabeled l t)  = isXType l <||> isXType t
isXType (TRow ts)       = or <$> mapM isXType ts
isXType (TConApp _ t)   = isXType t
isXType (TMap t)        = isXType t
isXType (TCompl y z)    = isXType y <||> isXType z
isXType TString         = return False
isXType (TInst is t)    = return True
isXType (TMapApp t)     = isXType t
isXType (TPlus x y)     = isXType x <||> isXType y
isXType (TConOrd _ _ t) = isXType t

isXPred :: MonadIO m => Pred -> m Bool
isXPred (PLeq x y)    = isXType x <||> isXType y
isXPred (PPlus x y z) = isXType x <||> isXType y <||> isXType z
isXPred (PEq t u)     = isXType t <||> isXType u
isXPred (PFold z)     = isXType z


-- ==============================================================================
-- Contexts
-- ==============================================================================

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
lookupV _ []           = error "lookupV: index out of range"
lookupV 0 ((_, t) : _) = t
lookupV n (_ : ts)     = lookupV (n - 1) ts

shiftE :: TCtxt -> TCtxt
shiftE = map (second (shiftN 0 1))

data TCIn = TCIn { kctxt :: KCtxt, tctxt :: TCtxt, pctxt :: PCtxt, level :: Level, ectxt :: Error -> Error }

emptyTCIn :: TCIn
emptyTCIn = TCIn [] [] [] 0 id

-- ==============================================================================
-- Tracking updates
-- ==============================================================================

data Creation where
  C :: Typeable a => IORef a -> Creation

sameRef :: Typeable a => IORef a -> Creation -> Bool
sameRef r (C r') =
  case cast r' of
    Nothing  -> False
    Just r'' -> r == r''

data Update where
  U :: IORef a -> a -> Update

perform :: MonadIO m => Update -> m ()
perform (U ref val) = liftIO $ writeIORef ref val

type Mark = Int

data TCSt = TCSt { references :: [(Mark, [Creation], [Update])], next :: Int }

pushCreation :: Typeable a => IORef a -> TCSt -> TCSt
pushCreation v st
  | [] <- references st = st
  | (m, cs, us) : rest <- references st = st { references = (m, C v : cs, us) : rest }

pushUpdate :: IORef a -> a -> TCSt -> TCSt
pushUpdate v x st
  | [] <- references st = st
  | (m, cs, us) : rest <- references st = st { references = (m, cs, U v x : us) : rest }

emptyTCSt :: TCSt
emptyTCSt = TCSt [] 0

-- ==============================================================================
-- Generated constraints
-- ==============================================================================

type Problem = (TCIn, Pred, IORef (Maybe Evid))
data TCOut = TCOut { goals :: [Problem], holes :: [(String, Ty, TCIn)] }

instance Semigroup TCOut where
  TCOut goals holes <> TCOut goals' holes' = TCOut (goals <> goals') (holes <> holes')

instance Monoid TCOut where
  mempty = TCOut mempty mempty

-- ==============================================================================
-- Type checker monads, with class
-- ==============================================================================

class (Monad m, MonadFail m, MonadRef m, MonadIO m, MonadReader TCIn m) => MonadCheck m where
  -----------------------------------------------------------------------------
  -- Environment management
  --
  -- We get default implementations in terms of the `MonadReader TCIn`
  -- superclass
  -----------------------------------------------------------------------------

  bindTy :: Kind -> m a -> m a
  bindTy k = local (\env -> env { kctxt = KBVar k (level env) : kctxt env, tctxt = shiftE (tctxt env), pctxt = map (shiftN 0 1) (pctxt env) })

  defineTy :: Kind -> Ty -> m a -> m a
  defineTy k t = local (\env -> env { kctxt = KBDefn k t : kctxt env, tctxt = shiftE (tctxt env), level = level env + 1 })

  bind :: String -> Ty -> m a -> m a
  bind x t m =
    do checkXType t
       local (\env -> env { tctxt = ([x, ""], t) : tctxt env }) m -- assuming that we only call `bind` with local variables

  assume :: Pred -> m a -> m a
  assume g m =
    do checkXPred "assuming" g
       local (\env -> env { pctxt = g : pctxt env }) m

  -----------------------------------------------------------------------------
  -- Generated constraints
  --
  -- We don't get a default implementation in terms of some assumed `MonadWriter
  -- TCOut m` superclass because `CheckM` does logging on `require`, whereas
  -- `UnifyM` does not.
  -----------------------------------------------------------------------------

  require :: Pred -> Goal Evid -> m ()

  -----------------------------------------------------------------------------
  -- Type errors
  -----------------------------------------------------------------------------

  typeError :: Error -> m a

  typeErrorContext :: (Error -> Error) -> m a -> m a
  typeErrorContext f = local (\env -> env { ectxt = ectxt env . f})

  -----------------------------------------------------------------------------
  -- Fresh name generation
  -----------------------------------------------------------------------------

  fresh :: String -> m String

  -----------------------------------------------------------------------------
  -- Levels
  --
  -- The level tracks the number of type binders we've passed under, and is used
  -- to avoid variable escape. Again, knowing `MonadReader TCIn` is enough.
  -----------------------------------------------------------------------------

  atLevel :: Level -> m t -> m t
  atLevel l = local (\st -> st { level = l })

  theLevel :: m Level
  theLevel = asks level

  -----------------------------------------------------------------------------
  -- Mark and reset
  --
  -- We want to be able to "undo" updates to unification variables in case
  -- unification fails, guesses need to be backtracked, and so forth. `mark`
  -- delimits let's call them epochs of updates, and reset restores the state to
  -- the point at a given mark.
  --
  -- As currently implemented, we only ever `reset` to the most recent `mark`,
  -- and only during unification. The more general structure here was to attempt
  -- to account for backtracking in predicate solving.
  -----------------------------------------------------------------------------

  mark :: m Mark
  reset :: Mark -> m ()

-- -----------------------------------------------------------------------------
-- Goal management
--
-- Actually, the reason we want `MonadRef` for type checker monads is all to do
-- with goals. We only have `MonadRef` in the first place, it turns out, because
-- `newGoal` really does want to have access to freshening, but `MonadRef` can
-- be defined for `IO` (which doesn't).
-- -----------------------------------------------------------------------------

newGoal :: (Typeable a, MonadCheck m) => String -> m (Goal a)
newGoal x =
  do x' <- fresh x
     v  <- newRef Nothing
     return (Goal (x', v))

readGoal :: MonadCheck m => Goal a -> m (Maybe a)
readGoal = readRef . goalRef

writeGoal g = writeRef (goalRef g) . Just

-- ==============================================================================
-- The actual type checker monad
-- ==============================================================================

newtype CheckM a = CM (WriterT TCOut (ReaderT TCIn (StateT TCSt (ExceptT Error IO))) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader TCIn, MonadState TCSt, MonadWriter TCOut)

-- Error handling is interesting because we apply the error context in the
-- environment to errors as they're generated.

instance MonadError Error CheckM where
  throwError e = do f <- asks ectxt
                    CM (throwError (f e))

  catchError e k = CM (catchError (unCM e) (unCM . k))
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

instance MonadCheck CheckM where
  require p g =
    do cin <- ask
       p' <- flatten p
       trace ("requiring " ++ show p')
       tell (TCOut [(cin, p, goalRef g)] [])

  typeError = throwError

  fresh x = do i <- gets next
               modify (\st -> st { next = i + 1 })
               return (takeWhile ('#' /=) x ++ '#' : show i)

  mark = do st <- get
            let m = next st
            put (st { references = (m, [], []) : references st, next = next st + 1})
            return m

  reset m = gets references >>= resetLoop where
    resetLoop [] =
      do modify (\st -> st { references = [] })
         return ()
    resetLoop ((m', _, us) : rest) =
      do mapM_ perform us
         when (m /= m') $ resetLoop rest

collect :: CheckM a -> CheckM (a, [Problem])
collect m = censor (\out -> out { goals = [] }) $
              second goals <$> listen m

upLevel :: MonadCheck m => m b -> m b
upLevel m = do l <- theLevel
               atLevel (l + 1) m

-- =============================================================================
-- The Unification monad
--
-- Unification differs from the checking monad in a couple of ways. First, we
-- keep a list of equations (assumptions) for unification, which passed on to
-- normalization. Second, we track the references introduced in the current
-- epoch. Third, we keep a collection of required predicates separately from the
-- underlying monad's required predicates, as unification may fail.
-- =============================================================================

type Eqn = (Ty, (Ty, Evid))

data AtomicHandler =
  AH { onTVar :: Int -> QName -> Ty -> UnifyM Evid
     , onUVar :: UVar -> Ty -> UnifyM Evid
     , onEq   :: Ty -> Ty -> UnifyM Evid }

type UR = AtomicHandler
type US = [Eqn]
type UW = [Problem]
newtype UnifyM a = UM { unUnifyM :: ExceptT UnificationError (StateT US (WriterT UW (ReaderT UR CheckM))) a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadWriter UW, MonadIO, MonadError UnificationError, MonadState US)

liftToUnifyM :: CheckM a -> UnifyM a
liftToUnifyM = UM . lift . lift . lift . lift

runUnifyM :: UnifyM a -> [Eqn] -> AtomicHandler -> CheckM (Either UnificationError a)
runUnifyM m eqns hs =
  do x <- mark
     (result, preds) <- runReaderT (runWriterT $ evalStateT (runExceptT $ unUnifyM m) eqns) hs
     case result of
       Right q ->
         do tell (TCOut preds [])
            return (Right q)
       Left err ->
         do reset x
            return (Left err)

instance MonadRef UnifyM where
  newRef = liftToUnifyM . newRef
  readRef = liftToUnifyM . readRef
  writeRef r v = liftToUnifyM (writeRef r v)

instance MonadReader TCIn UnifyM where
  ask = liftToUnifyM ask
  local f r = UM $ ExceptT $ StateT $ \eqns -> WriterT $ ReaderT $ \hs -> local f (runReaderT (runWriterT (runStateT (runExceptT (unUnifyM r)) eqns)) hs)

instance MonadCheck UnifyM where
  require p g =
    do cin <- ask
       tell [(cin, p, goalRef g)]

  mark = liftToUnifyM mark

  reset = liftToUnifyM . reset

  typeError = liftToUnifyM . typeError

  fresh = liftToUnifyM . fresh

theEqns :: UnifyM [Eqn]
theEqns = get

addEqn :: Eqn -> UnifyM ()
addEqn q = modify (q:)

solveTVar :: Int -> QName -> Ty -> UnifyM Evid
solveTVar i n u = UM $ do h <- asks onTVar
                          unUnifyM (h i n u)

solveUVar :: UVar -> Ty -> UnifyM Evid
solveUVar v u = UM $ do h <- asks onUVar
                        unUnifyM (h v u)

deferEq :: Ty -> Ty -> UnifyM Evid
deferEq t u = UM $ do h <- asks onEq
                      unUnifyM (h t u)

withHandler :: AtomicHandler -> UnifyM a -> UnifyM a
withHandler h m = UM (local (const h) (unUnifyM m))

unificationFails :: Ty -> Ty -> UnifyM a
unificationFails actual expected = throwError (TypesDon'tUnify actual expected)
