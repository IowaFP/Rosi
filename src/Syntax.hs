module Syntax (module Syntax, module Syntax.Common, module Syntax.Goals, module Syntax.Terms, module Syntax.Types, module Syntax.Vars) where

import Syntax.Common
import Syntax.Goals
import Syntax.Terms
import Syntax.Types
import Syntax.Vars

--------------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------------

data Program = Prog ([String], [Decl])
  deriving (Eq, Show)

data Decl = TyDecl QName Kind Ty | TmDecl QName (Maybe Ty) Term (Maybe Fixity)
  deriving (Eq, Show)







