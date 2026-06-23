{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module FixityResolution where

import Data.Foldable (find)

import Data.List     (intercalate)
import Printer       (renderPretty)
import Syntax
import qualified Debug.Trace as T

class DesugarInfix a where
  desugarInfix :: FixityMap -> a -> a

instance Ord EInfixToken where
  compare l@(Operator _ (Just f1)) r@(Operator _ (Just f2)) = compare f1 f2
  compare l r                                               = error $ "tried to compare invalid arguments " ++ show l ++ ", " ++ show r

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
  
  -- if fixity or associativity is mixed, or if both are non-associative, we use the precedence level
  -- (equal precedence is ambiguous)
  compare (Fixity _ l0) (Fixity _ l1) = compare l0 l1

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
  desugarInfix fixMap (EInfix _ops)        = (resolveFixitiesF . collectFixities . desugarInfix fixMap) _ops
    where
      collectFixities :: [EInfixToken] -> [EInfixToken]
      collectFixities = map (\ case (Operand e) -> Operand e
                                    (Operator qn _) -> Operator qn (Just (lookupFixity qn)))

      lookupFixity :: QName -> Fixity
      lookupFixity qname = maybe defaultFixity snd (find (lookFor qname . fst) fixMap)

      resolveFixitiesF :: [EInfixToken] -> Term
      resolveFixitiesF []       = error "resolveFixitiesF called with empty list"
      resolveFixitiesF exp = case resolveFixities [] [] exp of
                                    Right e           -> e
                                    Left (op1@(Operator _ fix1), op2@(Operator _ fix2))
                                      -> error $ "Could not resolve precedence between ("
                                              ++ renderPretty op1
                                              ++ ") ["
                                              ++ show fix1
                                              ++ "] and ("
                                              ++ renderPretty op2
                                              ++ ") ["
                                              ++ show fix2
                                              ++ "] in "
                                              ++ unwords (map renderPretty exp)
                                    Left (Operand e1, Operand e2) -> error $ "resolving infix operators resulted in adjacent expressions ("
                                                                           ++ renderPretty e1
                                                                           ++ ") and ("
                                                                           ++ renderPretty e2
                                                                           ++ ") in the context of the expression "
                                                                           ++ unwords (map renderPretty exp)
                                                                           ++ ". Use parentheses around adjacent expressions to avoid ambiguity."
                                    Left (op1, op2) -> error $ "resolveFixities tried to compare precedence between "
                                                            ++ show op1
                                                            ++ " and "
                                                            ++ show op2
                                                            ++ "in the context of the expression "
                                                            ++ unwords (map renderPretty exp)

      resolveFixities :: [EInfixToken] -> [Term] -> [EInfixToken] -> Either (EInfixToken, EInfixToken) Term

      -- Based on Garrett's algorithm from habit/alb and Djikstra's shunting yard algorithm,
      -- The presence of prefix and postfix operators means we can't assume that the expression consists of alternating operators and subterms.

      -- Invariants:
      -- Every operator below the top operator in the opStack has lower precedence
      -- Every term below the top term in the tmStack appears to its left
      -- Everything in opStack and tmStack appears to the left of everything in tail.

      -- resolveFixities a b c | T.trace (dumpStacks a b c) False = undefined
      -- error cases. Should be unreachable.
      resolveFixities [] [] [] = error "resolveFixities fixities called with all empty stacks"
      resolveFixities (op0@(Operator _ Nothing):ops) tms tail = error $ "resolveFixities fixities called with missing Fixity on an operator: " ++ show op0 ++ ". inputs = " ++ dumpStacks (op0:ops) tms tail
      resolveFixities ops tms (op1@(Operator _ Nothing):tail) = error $ "resolveFixities fixities called with missing Fixity on an operator: " ++ show op1 ++ ". inputs = " ++ dumpStacks ops tms (op1:tail)
      
      -- error case: if we end up with adjacent expressions on the term stack, fail.
      resolveFixities [] (e0:e1:es) [] = Left (Operand e1, Operand e0)

      -- Base case: we've successfully reduced to a term.
      resolveFixities [] [e] [] = Right e

      -- when head of tail is a term, push it on the term stack.
      resolveFixities ops tms ((Operand tm1):tail) = resolveFixities ops (tm1:tms) tail

      -- when opStack is empty, and head of tail is an operator, push it on opStack
      resolveFixities [] tms (op1@(Operator _ _):tail) = resolveFixities [op1] tms tail

      -- when tail is empty, pop from the opstack and apply to the top of tmStack
      resolveFixities (op0:ops) tmStack [] = resolveFixities ops (applyOp op0 tmStack) []

      -- when opStack is nonempty, and head of tail is an operator:
      resolveFixities (op0:ops) tmStack (op1@(Operator _ _):tail) =
        -- compare top of opStack with head of tail:
        case op0 `compare` op1 of
          -- if top of opstack takes precedence, apply it to top of tmStack
          GT -> resolveFixities ops (applyOp op0 tmStack) (op1:tail)
          -- if head of tail takes precedence push it onto opStack.
          LT -> resolveFixities (op1:op0:ops) tmStack tail
          EQ -> Left (op0, op1)

      app1 (Operator qn _) tm = EApp (EVar (-1) qn) tm
      app1 e tm               = error $ "tried to apply term " ++ show e ++ " to term " ++ show e
      app2 (Operator qn _) tm1 tm2 = EApp (EApp (EVar (-1) qn) tm1) tm2
      app2 e tm1 tm2               = error $ "tried to apply term " ++ show e ++ " to terms " ++ show tm1 ++ " and " ++ show tm2

      applyOp op [] = error $ "Can't apply op "
                                        ++ renderPretty op
                                        ++ " without a term to apply it to."
      applyOp op@(Operator _ (Just (Fixity Prefix _))) (tm:tms) = app1 op tm:tms
      applyOp op@(Operator _ (Just (Fixity Postfix _))) (tm:tms) = app1 op tm:tms
      applyOp op [tm0] = error $ "Expected two operands for "
                                        ++ renderPretty op
                                        ++ ", but there is only one on stack: "
                                        ++ renderPretty tm0
                                        ++ "\n (If you expect "
                                        ++ renderPretty op
                                        ++ " to be unary, make sure its fixity was declared."
      applyOp op (tm0:tm1:tms) = app2 op tm1 tm0 : tms

      fixityOf (Operator _ (Just (Fixity fx _))) = fx
      fixityOf op                                = error $ "fixityOf called with invalid token " ++ renderPretty op

      dumpStacks :: [EInfixToken] -> [Term] -> [EInfixToken] -> String
      dumpStacks opStack e tail = show ( intercalate " : " $ map renderPretty opStack, intercalate " : " $ map renderPretty e,  intercalate " : " $ map renderPretty tail)



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
  desugarInfix fixMap (TmDecl qn ty tm fx) = TmDecl qn ty (desugarInfix fixMap tm) fx
  desugarInfix fixMap x                 = x


desugarOperators decls = map (desugarInfix fixMap) decls where
  fixMap = [ (qn, fx) | (TmDecl qn _ _ (Just fx))<- decls]
