{-# OPTIONS_GHC -Wunused-imports #-}
module FixityResolution where

import Syntax
import Data.Foldable (find)

class DesugarInfix a where
  desugarInfix :: FixityMap -> a -> IO a


instance DesugarInfix Term where

  desugarInfix fixMap ((EVar n qname))    = return (EVar n qname)
  desugarInfix fixMap (ELam x ty tm)      = ELam x ty <$> desugarInfix fixMap tm
  desugarInfix fixMap (EApp ft xt)        = EApp <$> desugarInfix fixMap ft <*> desugarInfix fixMap xt

  desugarInfix fixMap (ETyLam s k tm )    = ETyLam s k <$> desugarInfix fixMap tm
  desugarInfix fixMap (EPrLam p tm)       = EPrLam p <$> desugarInfix fixMap tm
  desugarInfix fixMap (EInst tm insts)    = EInst <$> desugarInfix fixMap tm <*> pure insts

  desugarInfix fixMap (ESing ty)          = return $ ESing ty
  desugarInfix fixMap (ELabel tc lt xt)   = ELabel tc <$> desugarInfix fixMap lt <*> desugarInfix fixMap xt
  desugarInfix fixMap (EUnlabel tc xt lt) = EUnlabel tc <$> desugarInfix fixMap xt <*> desugarInfix fixMap lt

  desugarInfix fixMap (EConst c)          = return $ EConst c

  desugarInfix fixMap (ELet x vt et)      = ELet x <$> desugarInfix fixMap vt <*> desugarInfix fixMap et
  desugarInfix fixMap (ECast tm evid)     = ECast <$> desugarInfix fixMap tm <*> pure evid
  desugarInfix fixMap (ETyped tm ty)      = ETyped <$> desugarInfix fixMap tm <*> pure ty

  desugarInfix fixMap (EStringLit s)      = return $ EStringLit s
  desugarInfix fixMap (EHole s)           = return $ EHole s

  desugarInfix fixMap (EInfix ops)        = resolveFixities [] . collectFixities =<< desugarInfix fixMap ops
    where
      collectFixities :: [EInfixToken] -> [EInfixToken]
      collectFixities (Operand tm : ops) = Operand tm:collectFixities ops
      collectFixities (Operator qn _ : ops) = Operator qn (Just (fixityOf qn)) :collectFixities ops
      collectFixities ops = ops


      -- TODO(mctano) handle
        -- fixities
        -- precedence level
      resolveFixities :: [EInfixToken] -> [EInfixToken] -> IO Term

      resolveFixities [] [] = error "resolveFixities called with empty tail"
      resolveFixities [] [Operand tm] = pure tm
      resolveFixities [Operator qn (Just fxty), Operand lhs] [Operand rhs] = pure (EApp (EApp (EVar (-1) qn) lhs) rhs)
      resolveFixities [] ((Operand tm):(Operator qn (Just fxty)):rhs) =
        case fxty of
          Fixity InfixL _ -> EApp (EApp (EVar (-1) qn) tm) <$> resolveFixities [] rhs
          Fixity InfixR _ -> undefined
          Fixity Infix _  -> undefined
          Fixity Prefix _ -> undefined
          Fixity Postfix _ -> undefined
      resolveFixities [] ((Operator qn (Just fxty)):(Operand tm):rhs) =
        case fxty of
          Fixity InfixL _ -> undefined
          Fixity InfixR _ -> undefined
          Fixity Infix _  -> undefined
          Fixity Prefix _ -> undefined
          Fixity Postfix _ -> undefined
      resolveFixities [] [Operator qn (Just fxty)] = error $ "resolveFixities called with just an operator: " ++ show qn
      resolveFixities ((Operator qn (Just fxty)):(Operand tm):lhs) rhs =
        case fxty of
          Fixity InfixL _ -> undefined
          Fixity InfixR _ -> undefined
          Fixity Infix _  -> undefined
          Fixity Prefix _ -> undefined
          Fixity Postfix _ -> undefined
      resolveFixities lhs rhs = error $ "unexpected input to resolveFixities: " ++ show (lhs, rhs)

      fixityOf :: QName -> Fixity
      fixityOf qname = maybe defaultFixity snd (find (lookFor qname . fst) fixMap)

lookFor :: QName -> QName -> Bool
lookFor [x] (y : ys) = x == y
lookFor xs ys        = xs == ys

instance DesugarInfix [EInfixToken] where
  desugarInfix :: FixityMap -> [EInfixToken] -> IO [EInfixToken]
  desugarInfix fixMap []                 = pure []
  desugarInfix fixMap ((Operand tm):ops) = do tm' <- desugarInfix fixMap tm
                                              (Operand tm' :) <$> desugarInfix fixMap ops
  desugarInfix fixMap (op:ops)           =             (op :) <$> desugarInfix fixMap ops


instance DesugarInfix Decl where
  desugarInfix fixMap (TmDecl qn ty tm) = TmDecl qn ty <$> desugarInfix fixMap  tm
  desugarInfix fixMap x                    = return x

instance DesugarInfix [Decl] where
  desugarInfix fixMap = mapM (desugarInfix fixMap)
