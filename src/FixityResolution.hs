{-# OPTIONS_GHC -Wunused-imports #-}
module FixityResolution where

import Data.Foldable (find)
import Data.List     (intercalate)
import Debug.Trace   qualified as T
import Printer       (Printable (ppr), renderString)
import Syntax

class DesugarInfix a where
  desugarInfix :: FixityMap -> a -> a

instance Ord EInfixToken where
  compare l@(Operator _ (Just f1)) r@(Operator _ (Just f2)) = compare f1 f2
  compare l r                                               = error $ "tried to compare invalid arguments " ++ show l ++ ", " ++ show r

instance Ord Fixity where
  compare (Fixity InfixL l1) (Fixity InfixL l2) | l1 == l2 = GT
  compare (Fixity InfixR l1) (Fixity InfixR l2) | l1 == l2 = LT
  compare (Fixity _  l1) (Fixity _ l2) = compare l1 l2


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
  desugarInfix fixMap (EInfix ops)        = (resolveFixitiesF . collectFixities . desugarInfix fixMap) ops
    where
      collectFixities :: [EInfixToken] -> [EInfixToken]
      collectFixities = map (\ case (Operand e) -> Operand e
                                    (Operator qn _) -> Operator qn (Just (fixityOf qn)))

      fixityOf :: QName -> Fixity
      fixityOf qname = maybe defaultFixity snd (find (lookFor qname . fst) fixMap)

      resolveFixitiesF :: [EInfixToken] -> Term
      resolveFixitiesF exp@((Operand op):ops) = case resolveFixities [] op ops of
                                    Right e           -> e
                                    Left p@(op1@(Operator _ fix1), op2@(Operator _ fix2))
                                      -> error $ "Could not resolve precedence between ("
                                              ++ (renderString . ppr) op1
                                              ++ ") ["
                                              ++ show fix1
                                              ++ "] and ("
                                              ++ (renderString . ppr) op2
                                              ++ ") ["
                                              ++ show fix2
                                              ++ "] in "
                                              ++ unwords (map (renderString . ppr) exp)
                                              
      resolveFixitiesF []       = error "resolveFixitiesF called with empty list"

      resolveFixities :: [EInfixToken] -> Term -> [EInfixToken] -> Either (EInfixToken, EInfixToken) Term

      -- Based on Garrett's algorithm from habit/alb
      
      -- TODO(mctano) Do prefix/postfix operators mean we might have adjacent terms after eliminating them? And does that mean I'll have to do a round of application resolution after all this?

      -- Invariants:
      -- Every operator below the top operator in the stack has lower precedence

      -- Base case: we've successfully reduced to a term.
      resolveFixities [] e [] = Right e
      -- when stack is empty, push the current term and next operator onto the stack
      resolveFixities [] e (op1@(Operator _ _):(Operand e1):tail) = resolveFixities [op1, Operand e] e1 tail
      -- when right side is empty,
      -- the current term must be an argument to the top operator in the stack.
      -- and (by invariant) the operator has the highest precedence in the stack
      -- so, if the operator is infix, it must take e0 and e as operands.
      resolveFixities (op0@(Operator qn (Just fix0)): Operand e0:stack) e [] =
        -- dubious case (what if another operator was supposed to take precedence over the prefix?)
        case fix0 of
        -- this is actually illegal because popping the operator means we have adjacent terms.
        Fixity Prefix _  ->
          resolveFixities (Operand e0:stack) (app1 op0 e) []
          -- error "OOPS"
        Fixity Postfix _ -> error $ "Encountered postfix operator " ++ show op0 ++ " in illegal position."
        _                -> resolveFixities stack (app2 op0 e0 e) []
      
      -- -- happy case
      resolveFixities wholeStack@(op0@(Operator _ (Just fix0)) : Operand e0 : stack) e wholeTail@(op1@(Operator _ (Just fix2)) : (Operand e1) : op2@(Operator _ (Just fix3)) : tail) =
        -- TODO(mctano) handle pre/postfix
          case op0 `compare` op1 of
                  --  - The operator at the top of the stack binds more tightly than that at the top of the
                  --    tail.  In that case, we pop (e0, op0) from the stack, replace the current expression
                  --    with (e0 op0 e), and loop;
                  -- TODO(mctano) handle pre/postfix
                  GT -> resolveFixities stack (app2 op0 e0 e) (op1:Operand e1:op2:tail)
                  LT -> case op1 `compare` op2 of
                            --  - The operator at the top of the tail binds more tightly than either the operator at
                            --    the top of the stack or the operator following it in the tail.  In that case, we pop
                            --    (op1, e1) from the tail, replace the current expression with (e op1 e1), and loop;
                            GT -> resolveFixities (op0:Operand e0:stack) (app2 op1 e e1) (op2:tail)
                            --  - The second operator in the tail binds more tightly than either of the others; in
                            --    that case, we pop (op1, e1) from the tail, push (e, op1) onto the stack, and loop
                            --    with e1 as the current expression.
                            LT -> resolveFixities (op1:Operand e:op0:Operand e0:stack) e1 (op2:tail)
                            _  -> T.trace (show (concatMap (renderString . ppr) wholeStack, (renderString . ppr) e, concatMap (renderString . ppr) wholeTail)) Left (op1, op2)
                  EQ -> T.trace (show (concatMap (renderString . ppr) wholeStack, (renderString . ppr) e, concatMap (renderString . ppr) wholeTail)) Left (op0, op1)

      resolveFixities wholeStack@(op0@(Operator _ _):Operand e0:stack) e wholeTail@[op1@(Operator qnR fxR), Operand e1] =
        case op0 `compare` op1 of
          -- TODO(mctano) handle pre/postfix
          GT -> resolveFixities stack (app2 op0 e0 e) [op1, Operand e1]
          LT -> resolveFixities (op0:Operand e0:stack) (app2 op1 e e1) []
          EQ -> T.trace (show (concatMap (renderString . ppr) wholeStack, (renderString . ppr) e, concatMap (renderString . ppr) wholeTail)) Left (op0, op1)


      resolveFixities stack e wholeTail@(Operand e1:tail) = T.trace (show (concatMap (renderString . ppr) stack, (renderString . ppr) e, concatMap (renderString . ppr) wholeTail)) Left (Operand e, Operand e1)
      resolveFixities (Operand e0:stack) e tail = error $ "encountered adjacent terms " ++ show e0 ++ ", " ++ show e
      -- resolveFixities ((Operand e0):stack) e ((Operator qnR fxR):tail) = undefined
      resolveFixities stack e tail = error $ "unexpected input to resolveFixities: " ++ show (stack, e, tail)

      app1 (Operator qn _) = EApp (EVar (-1) qn)
      app2 (Operator qn _) e0 = EApp (EApp (EVar (-1) qn) e0)

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
  desugarInfix fixMap x                 = x

instance DesugarInfix [Decl] where
  desugarInfix fixMap = map (desugarInfix fixMap)
