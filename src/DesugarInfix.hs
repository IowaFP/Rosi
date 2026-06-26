{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module DesugarInfix where


import Data.List (intercalate)
import Errors
import Printer   (Printable, renderPretty)
import Syntax

class DesugarInfix a where
  desugarInfix :: a -> Either Error a

instance DesugarInfix Term where

  desugarInfix :: Term -> Either Error Term
  desugarInfix (EVar n qname)      = return $ EVar n qname
  desugarInfix (ELam x ty tm)      = ELam x ty <$> desugarInfix tm
  desugarInfix (EApp ft xt)        = EApp <$> desugarInfix ft <*> desugarInfix xt

  desugarInfix (ETyLam s k tm )    = ETyLam s k <$> desugarInfix tm
  desugarInfix (EPrLam p tm)       = EPrLam p <$> desugarInfix tm
  desugarInfix (EInst tm insts)    = (`EInst` insts) <$> desugarInfix tm

  desugarInfix (ESing ty)          = return $ ESing ty
  desugarInfix (ELabel tc lt xt)   = ELabel tc <$> desugarInfix lt <*> desugarInfix xt
  desugarInfix (EUnlabel tc xt lt) = EUnlabel tc <$> desugarInfix xt <*> desugarInfix lt

  desugarInfix (EConst c)          = return $ EConst c

  desugarInfix (ELet x vt et)      = ELet x <$> desugarInfix vt <*> desugarInfix et
  desugarInfix (ECast tm evid)     = (`ECast` evid) <$> desugarInfix tm
  desugarInfix (ETyped tm ty)      = (`ETyped` ty) <$> desugarInfix tm

  desugarInfix (EStringLit s)      = return $ EStringLit s
  desugarInfix (EHole s)           = return $ EHole s

                                          -- we make the recursive call to desugar subterms before collecting and resolving fixities
  desugarInfix (EInfix _ops)        = do ops' <- desugarInfix _ops
                                         let ops'' = padWithApply . collectFixities $ ops'
                                         resolveFixitiesF ops''
    where
      collectFixities :: [EInfixToken] -> [EInfixToken]
      collectFixities = map (\case (Operand e)                  -> Operand e
                                   (Operator todo qn Nothing)   -> Operator todo qn (Just defaultFixity)
                                   (Operator todo qn (Just fx)) -> Operator todo qn (Just fx)
                            )


      padWithApply []                                                                                                = []
      padWithApply (Operand tm : op@(Operator _ _ (Just (Fixity Prefix _))) : xs)                                    = Operand tm : explicitApp : op : padWithApply xs
      padWithApply (op@(Operator _ _ (Just (Fixity Postfix _))) : Operand tm : xs)                                   = op : explicitApp : padWithApply (Operand tm : xs)
      padWithApply (op0@(Operator _ _ (Just (Fixity Postfix _))) : op1@(Operator _ _ (Just (Fixity Prefix _))) : xs) = op0 : explicitApp : op1 : padWithApply xs

      padWithApply (x : xs)                                                                                          = x : padWithApply xs

      resolveFixitiesF :: [EInfixToken] -> Either Error Term
      resolveFixitiesF []       = error "resolveFixitiesF called with empty list"
      resolveFixitiesF exp = either
                                        report
                                        pure
                                        (resolveFixities [] [] exp)
                                        where
                                          report (l, r) = Left $ ErrInfixDesugaring (AmbiguousPrecedenceError l r exp)

      resolveFixities :: [EInfixToken] -> [AppTerm] -> [EInfixToken] -> Either (EInfixToken, EInfixToken) Term

      -- Based on Garrett's algorithm from habit/alb and Djikstra's shunting yard algorithm,
      -- The presence of prefix and postfix operators means we can't assume that the expression consists of alternating operators and subterms.

      -- Invariants:
      -- Every operator below the top operator in the opStack has lower precedence
      -- Every term below the top term in the tmStack appears to its left
      -- Everything in opStack and tmStack appears to the left of everything in tail.

      -- resolveFixities a b c | T.trace (dumpStacks a b c) False = undefined
      -- error cases. Should be unreachable.
      resolveFixities [] [] [] = error "internal: resolveFixities fixities called with all empty stacks"
      resolveFixities (op0@(Operator _ _ Nothing):ops) tms tail = error $ concat [
        "internal: resolveFixities fixities called with missing Fixity on an operator: " , show op0 , ". inputs = " , dumpStacks (op0:ops) tms tail]
      resolveFixities ops tms (op1@(Operator _ _ Nothing):tail) = error $ concat [
        "internal: resolveFixities fixities called with missing Fixity on an operator: " , show op1 , ". inputs = " , dumpStacks ops tms (op1:tail)]

      -- error case: if we end up with adjacent expressions on the term stack, fail.
      resolveFixities [] (e0:e1:es) [] = Left (Operand e1, Operand e0)

      -- Base case: we've successfully reduced to a term.
      resolveFixities [] [ATerm tm] [] = Right tm
      resolveFixities [] [AType t] [] = error $ "internal: ended up with a type in term position. " ++ show t

      -- when head of tail is a term, push it on the term stack.
      resolveFixities ops tms ((Operand tm1):tail) = resolveFixities ops (tm1:tms) tail

      -- when opStack is empty, and head of tail is an operator, push it on opStack
      resolveFixities [] tms (op1@(Operator {}):tail) = resolveFixities [op1] tms tail

      -- when tail is empty, pop from the opstack and apply to the top of tmStack
      resolveFixities (op0:ops) tmStack [] = resolveFixities ops (applyOp op0 tmStack) []

      -- when opStack is nonempty, and head of tail is an operator:
      resolveFixities (op0:ops) tmStack (op1@(Operator {}):tail) =
        -- compare top of opStack with head of tail:
        case op0 `compare` op1 of
          -- if top of opstack takes precedence, apply it to top of tmStack
          GT -> resolveFixities ops (applyOp op0 tmStack) (op1:tail)
          -- if head of tail takes precedence push it onto opStack.
          LT -> resolveFixities (op1:op0:ops) tmStack tail
          EQ -> Left (op0, op1)

      app1 (Operator i qn _) (AType ty) = error $ "tried to illegally apply term-level operator to type " ++ show ty
      app1 (Operator i qn _) (ATerm tm) = ATerm $ EApp (EVar i qn) tm
      app1 e tm                         = error $ "internal: tried to illegally apply expression " ++ show e ++ " to expression " ++ show e
      -- eliminate explicit application
      app2 (Operator _ ["__Apply"] _) (ATerm t) (AType u)     = ATerm (EInst t (Known [TyArg u]))
      app2 (Operator _ ["__Apply"] _) (ATerm tm1) (ATerm tm2) = ATerm $ EApp tm1 tm2
      app2 (Operator i qn _) (ATerm tm1) (ATerm tm2)          = ATerm (EApp (EApp (EVar i qn) tm1) tm2)
      app2 e tm1 tm2                                          = error $ concat ["internal: tried to illegally apply expression ", show e, " to expressions ", show tm1, " expressions ", show tm2]

      applyOp op [] = error $ "Can't apply op "
                                        ++ renderPretty op
                                        ++ " without a term to apply it to."
      applyOp op@(Operator _ _ (Just (Fixity Prefix _))) (tm:tms) = app1 op tm:tms
      applyOp op@(Operator _ _ (Just (Fixity Postfix _))) (tm:tms) = app1 op tm:tms
      -- TODO(mctano) convert the rest of these user errors to proper errors.
      applyOp op [tm0] = error $ concat ["Expected two operands for ", renderPretty op
                                        , ", but there is only one on stack: ", renderPretty tm0
                                        , "\n (If you expect " , renderPretty op
                                        , " to be unary, make sure its fixity was declared."]
      applyOp op (tm0:tm1:tms) = app2 op tm1 tm0 : tms

      fixityOf (Operator _ _ (Just (Fixity fx _))) = fx
      fixityOf op                                  = error $ "internal: fixityOf called with invalid token " ++ renderPretty op

      dumpStacks :: [EInfixToken] -> [AppTerm] -> [EInfixToken] -> String
      dumpStacks opStack e tail = show (pprStack opStack, pprStack e, pprStack tail)

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
