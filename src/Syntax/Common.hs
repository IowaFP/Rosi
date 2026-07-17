module Syntax.Common where

import Data.Generics (Data, Typeable)
import Data.IORef

--------------------------------------------------------------------------------
-- Names
--
-- Qualified names are stored in reverse order ("Data.Nat.zero" --> ["zero",
-- "Nat", "Data"]). Local names are signified with an empty list ["zero", ""].
--------------------------------------------------------------------------------

type Name = String
type QName = [Name]

--------------------------------------------------------------------------------
-- Goals
--
-- Goals represent problems to be solved during type inference, kind inference,
-- or predicate solving.
--------------------------------------------------------------------------------

newtype Goal t = Goal (String, IORef (Maybe t))
  deriving (Data, Typeable)

goalName :: Goal t -> String
goalName (Goal (s, _)) = s

goalRef :: Goal t -> IORef (Maybe t)
goalRef (Goal (_, r)) = r

instance Eq (Goal t) where
  Goal (x, _) == Goal (y, _) = x == y

instance Show (Goal t) where
  show (Goal (x, _)) = x

-- Abstract handling of goal references, so that we may later choose to (e.g.)
-- log and/or revert solutions to goals.

class Monad m => MonadRef m where
  readRef :: IORef a -> m a
  writeRef :: Typeable a => IORef a -> a -> m ()
  newRef :: Typeable a => a -> m (IORef a)

instance MonadRef IO where
  readRef = readIORef
  writeRef = writeIORef
  newRef = newIORef


--------------------------------------------------------------------------------
-- Fixities
--------------------------------------------------------------------------------

data FixityKind = InfixL | InfixR | Infix | Prefix | Postfix
  deriving (Data, Eq, Show)

data Fixity = Fixity FixityKind Int
  deriving (Data, Eq, Show)

instance Ord Fixity where
  -- associativity applies when infix level is equal
  compare (Fixity InfixL l0) (Fixity InfixL l1) | l0 == l1 = GT
  compare (Fixity InfixR l0) (Fixity InfixR l1) | l0 == l1 = LT

  -- prefix on the right binds tight
  -- thus adjacent prefixes associate right, regardless of precedence level
  -- consider that in (P \/ ! Q), the ! must apply to  Q, even if \/ has higher precedence
  compare (Fixity _ _) (Fixity Prefix _)  = LT

  -- similarly, postfix on the left binds tight
  -- thus adjacent postfixes associate left, regardless of precedence level
  compare (Fixity Postfix _) (Fixity _ _) = GT

  -- otherwise, we use the precedence level
  -- (equal precedence is ambiguous)
  compare (Fixity _ l0) (Fixity _ l1) = compare l0 l1

