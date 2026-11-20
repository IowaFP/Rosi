{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# OPTIONS_GHC -Werror=overlapping-patterns #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=40 #-}

module DesugarPatterns where


import Data.Bifunctor (first)
import Errors
import Syntax

class DesugarPatterns a where
  desugarPatterns :: a -> Either Error a

instance DesugarPatterns Term where

  desugarPatterns :: Term -> Either Error Term
  desugarPatterns (EVar n qname)       = return $ EVar n qname
  desugarPatterns (ELam x mty tm)       = desugarLamPattern x mty <$> desugarPatterns tm
  desugarPatterns (EApp ft xt)         = EApp <$> desugarPatterns ft <*> desugarPatterns xt

  desugarPatterns (ETyLam s k tm )     = ETyLam s k <$> desugarPatterns tm
  desugarPatterns (EExLam xs ps y t m) = EExLam xs ps y t <$> desugarPatterns m
  desugarPatterns (EPrLam p tm)        = EPrLam p <$> desugarPatterns tm
  desugarPatterns (EInst tm insts)     = (`EInst` insts) <$> desugarPatterns tm

  desugarPatterns (ESing ty)           = return $ ESing ty
  desugarPatterns (ELabel tc lt xt)    = ELabel tc <$> desugarPatterns lt <*> desugarPatterns xt
  desugarPatterns (EUnlabel tc xt lt)  = EUnlabel tc <$> desugarPatterns xt <*> desugarPatterns lt

  desugarPatterns (EConst c)           = return $ EConst c

  desugarPatterns (ELet x vt et)       = do et' <- desugarPatterns et
                                            vt' <- desugarPatterns vt
                                            let f =desugarLetPattern x
                                            return $ f vt' et'
      -- ($ Nothing) <$> desugarPattern x <*> desugarPatterns vt <*> desugarPatterns et
  desugarPatterns (ECast tm evid)      = (`ECast` evid) <$> desugarPatterns tm
  desugarPatterns (ETyped tm ty)       = (`ETyped` ty) <$> desugarPatterns tm

  desugarPatterns (EStringLit s)       = return $ EStringLit s
  desugarPatterns (EHole s)            = return $ EHole s

                                          -- we make the recursive call to desugar subterms before collecting and resolving fixities
  desugarPatterns (EInfix _ops)        = EInfix <$> desugarPatterns _ops

recordStr = "__RECORD"

-- parse top level of record pattern, then use helper for the interior pattern.
desugarLamPattern :: Binder -> (Maybe Ty -> Term -> Term)
desugarLamPattern x@(PatternVar _)       = ELam x
desugarLamPattern (PatternRecord fields) = \mty -> ELam (PatternVar recordStr) mty . desugarPatternFields fields

desugarLetPattern :: Binder -> (Term -> Term -> Term)
desugarLetPattern x@(PatternVar _) = ELet x
desugarLetPattern (PatternRecord fields) = \vt -> ELet (PatternVar recordStr) vt . desugarPatternFields fields

desugarPatternFields :: [(String, Binder)] -> (Term -> Term)
desugarPatternFields = foldr ((.) . (buildInnerBinding . buildPaths)) id

-- at each level, return a list of labels and the term that they map to.
-- with the returned value, prepend the current level's label to each of the lists.
buildPaths :: (String, Binder) -> [([String], String)]
buildPaths (l, PatternVar x)         = [([l], x)]
buildPaths (l, PatternRecord fields) = first (l :) <$> concatMap buildPaths fields

buildInnerBinding :: [([String], String)] -> (Term -> Term)
buildInnerBinding = foldr ((.) . bindPatternVar) id where
                  bindPatternVar (ls, x) = (ELet (PatternVar x) . toSel) ls
                  toSel = buildDeepSel recordVar . map labelFromString
                  recordVar = EVar (-1) [recordStr]
                  labelFromString = ESing . TLab


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
