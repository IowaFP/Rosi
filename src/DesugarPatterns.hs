{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# OPTIONS_GHC -Werror=overlapping-patterns #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=40 #-}

module DesugarPatterns where


import Errors
import Syntax
import Data.Bifunctor (first)

class DesugarPatterns a where
  desugarPatterns :: a -> Either Error a

-- TODO(mctano) try to do something about the amount of boilerplate required to write a desugaring pass.

instance DesugarPatterns Term where

  desugarPatterns :: Term -> Either Error Term
  desugarPatterns (EVar n qname)       = return $ EVar n qname
  desugarPatterns (ELam x ty tm)       = desugarPattern x ty <*> desugarPatterns tm
  desugarPatterns (EApp ft xt)         = EApp <$> desugarPatterns ft <*> desugarPatterns xt

  desugarPatterns (ETyLam s k tm )     = ETyLam s k <$> desugarPatterns tm
  desugarPatterns (EExLam xs ps y t m) = EExLam xs ps y t <$> desugarPatterns m
  desugarPatterns (EPrLam p tm)        = EPrLam p <$> desugarPatterns tm
  desugarPatterns (EInst tm insts)     = (`EInst` insts) <$> desugarPatterns tm

  desugarPatterns (ESing ty)           = return $ ESing ty
  desugarPatterns (ELabel tc lt xt)    = ELabel tc <$> desugarPatterns lt <*> desugarPatterns xt
  desugarPatterns (EUnlabel tc xt lt)  = EUnlabel tc <$> desugarPatterns xt <*> desugarPatterns lt

  desugarPatterns (EConst c)           = return $ EConst c

  desugarPatterns (ELet x vt et)       = ELet x <$> desugarPatterns vt <*> desugarPatterns et
  desugarPatterns (ECast tm evid)      = (`ECast` evid) <$> desugarPatterns tm
  desugarPatterns (ETyped tm ty)       = (`ETyped` ty) <$> desugarPatterns tm

  desugarPatterns (EStringLit s)       = return $ EStringLit s
  desugarPatterns (EHole s)            = return $ EHole s

                                          -- we make the recursive call to desugar subterms before collecting and resolving fixities
  desugarPatterns (EInfix _ops)        = EInfix <$> desugarPatterns _ops


desugarPattern :: Binder ->  Maybe Ty -> Either Error (Term -> Term)
desugarPattern x@(PatternVar _) ty = return $ ELam x ty
desugarPattern (PatternRecord fields) ty = return $ ELam (PatternVar "RECORD") ty . desugarPatternFields fields
  where
    desugarPatternFields :: [(String, Binder)] -> (Term -> Term)
    desugarPatternFields [] = id
    desugarPatternFields (p:ps) = (construct . findPaths) p . desugarPatternFields ps
desugarPattern (PatternVariant _) ty = error "TODO"

findPaths :: (String, Binder) -> [([String], String)]
findPaths (l, PatternVar x) = [([l], x)]
findPaths (l, PatternRecord fields) = let fieldPaths = map findPaths fields in map (first (l :)) (concat fieldPaths)
findPaths (l,p) = error "TODO"

construct :: [([String], String)] -> (Term -> Term)
construct = foldr g id where
                      g (ls, x) a = ELet x (buildDeepSel (EVar (-1) ["RECORD"]) (map (ESing . TLab) ls)) . a


-- desugar all subterms in the list of operators and operands
-- this must be called before passing the list of tokens to resolveFixities
-- to desugar Pattern operators at the current level
instance (DesugarPatterns a) => DesugarPatterns [a] where
  desugarPatterns = mapM desugarPatterns


instance DesugarPatterns EInfixToken where
  desugarPatterns (Operand tm) = Operand <$> desugarPatterns tm
  desugarPatterns op           = return op

instance DesugarPatterns AppTerm where
  desugarPatterns (ATerm tm) = ATerm <$> desugarPatterns tm
  desugarPatterns ty         = return ty


instance DesugarPatterns Decl where
  desugarPatterns (TmDecl qn ty tm fx) = TmDecl qn ty <$> desugarPatterns tm <*> pure fx
  desugarPatterns x                    = pure x
