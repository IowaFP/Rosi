{-# OPTIONS_GHC -Wunused-imports #-}
module FixityResolution where

import Data.Foldable (find)
import Syntax

class DesugarInfix a where
  desugarInfix :: FixityMap -> a -> a


instance DesugarInfix Term where

  desugarInfix fixMap (EVar n qname)      = EVar n qname
  desugarInfix fixMap (ELam x ty tm)      = ELam x ty (desugarInfix fixMap tm)
  desugarInfix fixMap (EApp ft xt)        = EApp (desugarInfix fixMap ft) (desugarInfix fixMap xt)

  desugarInfix fixMap (ETyLam s k tm )    = ETyLam s k (desugarInfix fixMap tm)
  desugarInfix fixMap (EPrLam p tm)       = EPrLam p (desugarInfix fixMap tm)
  desugarInfix fixMap (EInst tm insts)    = EInst (desugarInfix fixMap tm) insts

  desugarInfix fixMap (ESing ty)          = ESing ty
  desugarInfix fixMap (ELabel tc lt xt)   = ELabel tc (desugarInfix fixMap lt) (desugarInfix fixMap xt)
  desugarInfix fixMap (EUnlabel tc xt lt) = EUnlabel tc (desugarInfix fixMap xt) ( desugarInfix fixMap lt)

  desugarInfix fixMap (EConst c)          = EConst c

  desugarInfix fixMap (ELet x vt et)      = ELet x (desugarInfix fixMap vt) (desugarInfix fixMap et)
  desugarInfix fixMap (ECast tm evid)     = ECast (desugarInfix fixMap tm) evid
  desugarInfix fixMap (ETyped tm ty)      = ETyped (desugarInfix fixMap tm) ty

  desugarInfix fixMap (EStringLit s)      = EStringLit s
  desugarInfix fixMap (EHole s)           = EHole s

                                          -- we make the recursive call to desugar subterms before collecting and resolving fixities
  desugarInfix fixMap (EInfix ops)        = (resolveFixities [] . collectFixities . desugarInfix fixMap) ops
    where
      collectFixities :: [EInfixToken] -> [EInfixToken]
      collectFixities = map (\ case (Operand tm) -> Operand tm
                                    (Operator qn _) -> Operator qn (Just (fixityOf qn)))

      fixityOf :: QName -> Fixity
      fixityOf qname = maybe defaultFixity snd (find (lookFor qname . fst) fixMap)

      -- TODO(mctano) handle
        -- fixities
        -- precedence level
      resolveFixities :: [EInfixToken] -> [EInfixToken] -> Term

      resolveFixities [] [] = error "resolveFixities called with empty tail"
      resolveFixities [] [Operand tm] = tm
      resolveFixities [Operator qn (Just fxty), Operand lhs] [Operand rhs] = EApp (EApp (EVar (-1) qn) lhs) rhs
      resolveFixities [] ((Operand tm):(Operator qn (Just fxty)):rhs) =
        case fxty of
          Fixity InfixL _ -> EApp (EApp (EVar (-1) qn) tm) (resolveFixities [] rhs)
          Fixity InfixR _ -> undefined
          Fixity Infix _  -> undefined
          Fixity Prefix _ -> undefined
          Fixity Postfix _ -> undefined
      resolveFixities [] ((Operator qn (Just fxty)):(Operand tm):rhs) =
        case fxty of
          Fixity InfixL _  -> undefined
          Fixity InfixR _  -> undefined
          Fixity Infix _   -> undefined
          Fixity Prefix _  -> undefined
          Fixity Postfix _ -> undefined
      resolveFixities [] [Operator qn (Just fxty)] = error $ "resolveFixities called with just an operator: " ++ show qn
      resolveFixities ((Operator qn (Just fxty)):(Operand tm):lhs) rhs =
        case fxty of
          Fixity InfixL _  -> undefined
          Fixity InfixR _  -> undefined
          Fixity Infix _   -> undefined
          Fixity Prefix _  -> undefined
          Fixity Postfix _ -> undefined
      resolveFixities lhs rhs = error $ "unexpected input to resolveFixities: " ++ show (lhs, rhs)

lookFor :: QName -> QName -> Bool
lookFor [x] (y : ys) = x == y
lookFor xs ys        = xs == ys

-- desugar all subterms in the list of operators and operands
-- this must be called before passing the list of tokens to resolveFixities
-- to desugar infix operators at the current level
instance DesugarInfix [EInfixToken] where
  desugarInfix :: FixityMap -> [EInfixToken] -> [EInfixToken]
  desugarInfix fixMap = map (desugarInfix fixMap)


instance DesugarInfix EInfixToken where
  desugarInfix fixMap (Operand tm) = Operand (desugarInfix fixMap tm)
  desugarInfix fixMap op           = op


instance DesugarInfix Decl where
  desugarInfix fixMap (TmDecl qn ty tm) = TmDecl qn ty (desugarInfix fixMap tm)
  desugarInfix fixMap x                    = x

instance DesugarInfix [Decl] where
  desugarInfix fixMap = map (desugarInfix fixMap)
