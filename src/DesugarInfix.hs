{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# OPTIONS_GHC -Werror=overlapping-patterns #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=40 #-}

module DesugarInfix where


import Data.List (intercalate)
import Errors
import Printer   (Printable, renderPretty)
import Syntax

class DesugarInfix a where
  desugarInfix :: a -> Either Error a

instance DesugarInfix Term where

  desugarInfix :: Term -> Either Error Term
  desugarInfix (EVar n qname)       = return $ EVar n qname
  desugarInfix (ELam x ty tm)       = ELam x ty <$> desugarInfix tm
  desugarInfix (EApp ft xt)         = EApp <$> desugarInfix ft <*> desugarInfix xt

  desugarInfix (ETyLam s k tm )     = ETyLam s k <$> desugarInfix tm
  desugarInfix (EExLam xs ps y t m) = EExLam xs ps y t <$> desugarInfix m
  desugarInfix (EPrLam p tm)        = EPrLam p <$> desugarInfix tm
  desugarInfix (EInst tm insts)     = (`EInst` insts) <$> desugarInfix tm

  desugarInfix (ESing ty)           = return $ ESing ty
  desugarInfix (ELabel tc lt xt)    = ELabel tc <$> desugarInfix lt <*> desugarInfix xt
  desugarInfix (EUnlabel tc xt lt)  = EUnlabel tc <$> desugarInfix xt <*> desugarInfix lt

  desugarInfix (EConst c)           = return $ EConst c

  desugarInfix (ELet x vt et)       = ELet x <$> desugarInfix vt <*> desugarInfix et
  desugarInfix (ECast tm evid)      = (`ECast` evid) <$> desugarInfix tm
  desugarInfix (ETyped tm ty)       = (`ETyped` ty) <$> desugarInfix tm

  desugarInfix (EStringLit s)       = return $ EStringLit s
  desugarInfix (EHole s)            = return $ EHole s

                                          -- we make the recursive call to desugar subterms before collecting and resolving fixities
  desugarInfix (EInfix _ops)        = do ops' <- desugarInfix _ops
                                         let ops'' = padWithApply . collectFixities $ ops'
                                         resolveFixitiesF ops''
    where
      collectFixities :: [EInfixToken] -> [EInfixToken]
      collectFixities = map (\case (Operand e)                  -> Operand e
                                   (Operator (Op todo qn Nothing))   -> Operator (Op todo qn (Just defaultFixity))
                                   (Operator (Op todo qn (Just fx))) -> Operator (Op todo qn (Just fx))
                            )


      padWithApply []                                                                                                          = []
      padWithApply (Operand tm : op@(Operator (Op _ _ (Just (Fixity Prefix _)))) : xs)                                         = Operand tm : explicitApp : op : padWithApply xs
      padWithApply (op@(Operator (Op _ _ (Just (Fixity Postfix _)))) : Operand tm : xs)                                        = op : explicitApp : padWithApply (Operand tm : xs)
      padWithApply (op0@(Operator (Op _ _ (Just (Fixity Postfix _)))) : op1@(Operator (Op _ _ (Just (Fixity Prefix _)))) : xs) = op0 : explicitApp : op1 : padWithApply xs


      padWithApply (x : xs)                                                                                                    = x : padWithApply xs

      resolveFixitiesF :: [EInfixToken] -> Either Error Term
      resolveFixitiesF []       = error "internal: resolveFixitiesF called with empty list"

      resolveFixitiesF exp = either
                                        report
                                        pure
                                        (resolveFixities [] [] exp)
                                        where
                                          report err = Left $ ErrInfixDesugaring err exp

      resolveFixities :: [EOp] -> [AppTerm] -> [EInfixToken] -> Either InfixDesugaringError Term


      -- Based on Garrett's algorithm from habit/alb and Djikstra's shunting yard algorithm,
      -- The presence of prefix and postfix operators means we can't assume that the expression consists of alternating operators and subterms.

      -- Invariants:
      -- Every operator below the top operator in the opStack has lower precedence
      -- Every term below the top term in the tmStack appears to its left
      -- Everything in opStack and tmStack appears to the left of everything in tail.

      -- resolveFixities a b c | T.trace (dumpStacks a b c) False = undefined
      -- error cases. Should be unreachable.
      resolveFixities [] [] [] = error "internal: resolveFixities fixitieserror called with all empty stacks"
      resolveFixities [] [AType t] []        = error $ "internal: FixityResolution called with a sole type on tmStack. " ++ show t
      resolveFixities [] tmStack@(at:_:_) [] = error $ "internal: FixityResolution called with multiple appTerms on tmStack, but empty opStack and tail" ++ show tmStack

      -- Base case: we've successfully reduced to a term.
      resolveFixities [] [ATerm tm] [] = Right tm

      -- when head of tail is a term, push it on the term stack.
      resolveFixities ops tms ((Operand tm1):tail) = resolveFixities ops (tm1:tms) tail

      -- when opStack is empty, and head of tail is an operator, push it on opStack
      resolveFixities [] tms ((Operator op1):tail) = resolveFixities [op1] tms tail

      -- when tail is empty, pop from the opstack and apply to the top of tmStack
      resolveFixities (op0:ops) tmStack [] = do tmStack' <- applyOp op0 tmStack
                                                resolveFixities ops tmStack' []

      -- when opStack is nonempty, and head of tail is an operator:
      resolveFixities (op0:ops) tmStack ((Operator op1):tail) =
        -- compare top of opStack with head of tail:
        case op0 `compare` op1 of
          -- if top of opstack takes precedence, apply it to top of tmStack
          GT -> do tmStack' <- applyOp op0 tmStack
                   resolveFixities ops tmStack' (Operator op1:tail)
          -- if head of tail takes precedence push it onto opStack.
          LT -> resolveFixities (op1:op0:ops) tmStack tail
          EQ -> Left $ AmbiguousPrecedenceError op0 op1


      app1 :: EOp -> AppTerm -> Either InfixDesugaringError AppTerm
      app1 ( (Op i qn _)) (ATerm tm) = Right $ ATerm $ EApp (EVar i qn) tm
      app1 op@(Op i qn _) (AType ty) = Left $ IllegalApplyOpToTypeUnary op ty

      app2 :: EOp -> AppTerm -> AppTerm -> Either InfixDesugaringError AppTerm
      -- apply a term to a type
      app2 (Op _ ["__Apply"] _) (ATerm t) (AType u)     = Right $ ATerm (EInst t (Known [TyArg u]))
      -- apply a term to a term
      app2 (Op _ ["__Apply"] _) (ATerm tm1) (ATerm tm2) = Right $ ATerm $ EApp tm1 tm2
      -- apply an op to a term
      app2 ((Op i qn _)) (ATerm tm1) (ATerm tm2)        = Right $ ATerm (EApp (EApp (EVar i qn) tm1) tm2)

      -- error cases
      app2 ( (Op _ ["__Apply"] _)) (AType ty) e         = Left $ IllegalApplyTypeToAny ty e
      app2 op arg1@(AType _) arg2                       = Left $ IllegalApplyOpToTypeBinary op arg1 arg2
      app2 op arg1 arg2@(AType _)                       = Left $ IllegalApplyOpToTypeBinary op arg1 arg2



      applyOp :: EOp -> [AppTerm] -> Either InfixDesugaringError [AppTerm]

      applyOp op (tm:tms)      | arityOf op == 1      = (<$> app1 op tm) (:tms)
      applyOp op (tm0:tm1:tms) | arityOf op == 2      = (<$> app2 op tm1 tm0) (:tms)
      applyOp op tmStack                              = Left $ NotEnoughArguments op (arityOf op) tmStack


      fixityOf (Op _ _ (Just (Fixity fx _))) = fx
      fixityOf op                            = error $ "internal: fixityOf called with invalid token " ++ renderPretty op


      arityOf op                             = if fixityOf op `elem` [Prefix, Postfix] then 1 else 2


      dumpStacks :: [EInfixToken] -> [AppTerm] -> [EInfixToken] -> String
      dumpStacks opStack tmStack tail = show (pprStack opStack, pprStack tmStack, pprStack tail)


      pprStack :: Printable a => [a] -> String
      pprStack = intercalate " : " . map renderPretty

-- desugar all subterms in the list of operators and operands
-- this must be called before passing the list of tokens to resolveFixities
-- to desugar infix operators at the current level
instance (DesugarInfix a) => DesugarInfix [a] where
  desugarInfix = mapM desugarInfix


instance DesugarInfix EInfixToken where
  desugarInfix (Operand tm) = Operand <$> desugarInfix tm
  desugarInfix op           = return op

instance DesugarInfix AppTerm where
  desugarInfix (ATerm tm) = ATerm <$> desugarInfix tm
  desugarInfix ty         = return ty


instance DesugarInfix Decl where
  desugarInfix (TmDecl qn ty tm fx) = TmDecl qn ty <$> desugarInfix tm <*> pure fx
  desugarInfix x                    = pure x
