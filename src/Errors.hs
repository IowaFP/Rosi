module Errors where
import Syntax
--------------------------------------------------------------------------------
-- Type errors
--
-- Probably ought to live somewhere else
--------------------------------------------------------------------------------

data Error = ErrContextDefn QName Error | ErrContextType Ty Error | ErrContextTerm Term Error | ErrContextPred Pred Error | ErrContextOther String Error
           | ErrContextTyEq Ty Ty Error
           | ErrTypeMismatch Ty Ty Ty Ty | ErrTypeMismatchFD Pred | ErrTypeMismatchPred Pred Ty Ty | ErrKindMismatch Kind Kind
           | ErrNotEntailed [(Pred, [Pred])]
           | ErrTypeDesugaring Ty 
             -- Error which occurred during Infix Resolution, plus the EInfix expression where it occured.
           | ErrInfixDesugaring InfixDesugaringError [EInfixToken]
           | ErrUnboundVar QName | ErrUnboundTyVar QName | ErrDuplicateDefinition QName
           | ErrOther String

data InfixDesugaringError =
  AmbiguousPrecedenceError EOp EOp 
  | IllegalApplyTypeToAny Ty AppTerm
  | IllegalApplyOpToTypeUnary EOp Ty
  | IllegalApplyOpToTypeBinary EOp AppTerm AppTerm
  | NotEnoughArguments EOp Int [AppTerm]
  | OtherInfixResolutionError String
