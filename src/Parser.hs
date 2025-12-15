{-# LANGUAGE DeriveDataTypeable #-}
module Parser where

import Syntax

import Control.Monad (foldM, guard, mplus, replicateM, void, when)
-- import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader
import Control.Monad.State

import Data.Char (isSpace)
import Data.Data
import Data.IORef (newIORef)
import Data.List (delete, intercalate)
import Data.List.NonEmpty (fromList)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import Data.Void (Void)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as P
import Text.Megaparsec.Error

import Debug.Trace

--------------------------------------------------------------------------------
-- Combinators I miss from Parsec

terminal p = p <* eof

chainr1 p op =
  do lhs <- p
     rhss <- many (do f <- op
                      rhs <- p
                      return (f, rhs))
     return (down lhs rhss)
  where down lhs [] = lhs
        down lhs ((op, rhs) : rhss) = op lhs (down rhs rhss)

chainl1 p op =
  do lhs <- p
     rhss <- many (do f <- op
                      rhs <- p
                      return (f, rhs))
     return (down lhs rhss)
  where down lhs [] = lhs
        down lhs ((op, rhs) : rhss) = down (op lhs rhs) rhss

ps :: Show t => Parser t -> String -> IO ()
ps p s = putStrLn $ either errorBundlePretty show $ evalState (runParserT p "" s) []

--------------------------------------------------------------------------------

type Parser = ParsecT Void [Char] (State [(Ordering, Pos)])

pushIndent :: Ordering -> Pos -> Parser ()
pushIndent o n = lift (modify ((o, n) :))

popIndent :: Parser ()
popIndent = lift (modify tail)

theIndent :: Parser (Maybe (Ordering, Pos))
theIndent =
  do is <- lift get
     case is of
       [] -> return Nothing
       i : _ -> return (Just i)

guardIndent :: Parser a -> Parser a
guardIndent p =
  do indent <- theIndent
     case indent of
       Nothing -> p
       Just (ord, goal) ->
         do here <- P.indentLevel
            when (compare here goal /= ord) (P.incorrectIndent ord goal here)
            p

item :: Parser a -> (a -> Parser b) -> Parser b
item p q =
  do here <- P.indentLevel
     x <- p
     pushIndent GT here
     q x <* popIndent

at goal p =
  do here <- P.indentLevel
     when (here /= goal) (P.incorrectIndent EQ goal here)
     p

block :: Parser a -> Parser [a]
block p =
  do here <- P.indentLevel
     pushIndent EQ here
     many p <* popIndent

{-------------------------------------------------------------------------------

Binder should be provided in *source* order. That is, if you have

    \ x y z. M

The binder list should be provided as ["x", "y", "z"]

-------------------------------------------------------------------------------}

--------------------------------------------------------------------------------
-- Lexer, Megaparsec style

whitespace :: Parser ()
whitespace = P.space space1 (P.skipLineComment "--") (P.skipBlockCommentNested "{-" "-}")

--------------------------------------------------------------------------------
-- Shorthand

lexeme p    = guardIndent p <* whitespace

symbol      = lexeme . string
reserved s  = lexeme (try (string s <* notFollowedBy (alphaNumChar <|> char '\'')))

identifier  = lexeme ((:) <$> letterChar <*> many (alphaNumChar <|> char '\''))

qidentifier  =
  do x <- identifier
     xs <- many (try (string "." >> identifier))
     return (reverse (x : xs))

parens      = between (symbol "(") (symbol ")")
angles      = between (symbol "<") (symbol ">")
brackets    = between (symbol "[") (symbol "]")
braces      = between (symbol "{") (symbol "}")
semi        = symbol ";"
comma       = symbol ","
colon       = symbol ":"
dot         = symbol "."
semiSep     = flip sepBy semi
semiSep1    = flip sepBy1 semi
commaSep    = flip sepBy comma
commaSep1   = flip sepBy1 comma

number      = lexeme P.decimal
stringLit   = lexeme (char '"' >> manyTill P.charLiteral (char '"'))

---------------------------------------------------------------------------------
-- Parser

kind :: Parser Kind
kind = chainr1 akind (symbol "->" >> return KFun) where
  akind =  choice [ symbol "*" >> return KType
                  , symbol "L" >> return KLabel
                  , parens kind
                  , do symbol "R"
                       KRow <$> brackets kind ]

binders :: Parser t -> Parser [(String, Maybe t)]
binders p =
  do xs <- some identifier
     m <- optional $ do colon >> p
     return (map (, m) xs)

ty :: Parser Ty
ty = do pfs <- many prefix
        ty <- thenTy
        return (foldr ($) ty pfs) where
  prefix :: Parser (Ty -> Ty)
  prefix = choice
             [ do symbol "\\"
                  bs <- commaSep1 (binders kind)
                  dot
                  return (foldr (\(v, k) f -> TLam v k . f) id (concat bs))
             , do symbol "forall"
                  bs <- commaSep1 (binders kind)
                  dot
                  return (foldr (\(v, k) f -> TForall v k . f) id (concat bs)) ]

  thenTy :: Parser Ty
  thenTy = scan where
    scan :: Parser Ty
    scan = tyOrP >>= rest

    rest (Right t) = return t
    rest (Left ps)  = do symbol "=>"
                         t <- scan
                         return (foldr TThen t ps)
                    <|>
                      unexpected (Label $ fromList "predicate")

tyOrP :: Parser (Either [Pred] Ty)
tyOrP = Left <$> try (commaSep1 pr) <|> Right <$> arrTy

arrTy :: Parser Ty
arrTy = chainr1 labTy (symbol "->" >> return (\t u -> TApp (TApp TFun t) u))

labTy :: Parser Ty
labTy =
  do t <- minusTy
     choice
       [ do symbol ":="
            TLabeled t <$> ty
       , return t ]


  -- chainr1 minusTy (symbol ":=" *> return TLabeled)

minusTy :: Parser Ty
minusTy = chainl1 (apps <$> some atype) (lexeme (try (string "-" <* notFollowedBy (char '>'))) *> return (\t u -> TCompl t u))

apps :: [Ty] -> Ty
apps = foldl1 TApp

-- labTy = do t <- atype
--            choice
--              [ do symbol ":="
--                   (u : us) <- some atype
--                   return (TLabeled t (foldl TApp u us))
--              , do us <- many atype
--                   return (foldl TApp t us) ]
labeledTy =
  do t <- labTy
     case t of
       TLabeled _ _ -> return t
       _ -> unexpected (Label $ fromList "unlabeled type")

atype :: Parser Ty
atype = choice [ TLab <$> lexeme (char '\'' >> some alphaNumChar)
               , TSing <$> (char '#' >> atype)
               , TConApp Sigma <$> (symbol "Sigma" >> atype)
               , TConApp Pi <$> (symbol "Pi" >> atype)
               , TConApp Mu <$> (symbol "Mu" >> atype)
               , TRow <$> braces (commaSep labeledTy)
               , const TString <$> symbol "String"
               , (\x -> TVar (-1) x) <$> qidentifier
               , parens ty ]

pr :: Parser Pred
pr = choice [ do symbol "Fold"
                 PFold <$> arrTy
            , do t <- arrTy
                 choice
                   [ do symbol "<"
                        PLeq t <$> arrTy
                   , do symbol "+"
                        u <- arrTy
                        symbol "~"
                        PPlus t u <$> arrTy ] ]

-- We need a random precedence table here.  Let's try:
--
--     ++ ?
--     := /

term :: Parser Term
term = prefixes typedTerm where

  prefix :: Parser (Term -> Term)
  prefix = do symbol "\\"
              bs <- commaSep1 (binders ty)
              dot
              return (foldr1 (.) (map (uncurry ELam) (concat bs)))
         <|>
           do symbol "/\\"
              bs <- commaSep1 (binders kind)
              dot
              return (foldr1 (.) (map (uncurry ETyLam) (concat bs)))
         <|>
           do symbol "let"
              x <- identifier
              symbol "="
              t <- term
              symbol ";"
              return (ELet x t)

  prefixes :: Parser Term -> Parser Term
  prefixes rest =
    do mp <- optional (try prefix)
       case mp of
         Nothing -> rest
         Just f -> f <$> prefixes rest

  op s k = symbol s >> k

  typedTerm =
    do t <- branchTerm
       maybe t (ETyped t) <$> optional (symbol ":" >> ty)

  ebinary k = return (\e1 e2 -> EApp (EApp (EConst k) e1) e2)

  branchTerm = chainl1 labTerm $ choice [op "++" (ebinary CConcat) , op "|" (ebinary CBranch)]

  labTerm =
    do t <- catTerm
       choice
         [ do symbol ":="
              ELabel Nothing t <$> term
         , do symbol "/"
              EUnlabel Nothing t <$> catTerm
         , return t ]

    -- chainl1 catTerm $ choice [op ":=" (return ELabel), op "/" (return EUnlabel)]

  catTerm = chainl1 appTerm $ op "^" (ebinary CStringCat)

data AppTerm = Type Ty | Term Term

appTerm :: Parser Term
appTerm = do (t : ts) <- some (Type <$> brackets ty <|> Term <$> aterm)
             app t ts where
  app (Term t) [] = return t
  app (Type _) _ = unexpected (Label $ fromList "type argument")
  app (Term t) (Term u : ts) = app (Term (EApp t u)) ts
  app (Term t) (Type u : ts) = app (Term (EInst t (Known [TyArg u]))) ts
  goal s = Goal . (s,) <$> newIORef Nothing

  -- builtIns = choice (map builtIn ["prj", "inj", "ana", "syn", "(++)", "(?)", "in", "out", "fix"]) where

  aterm = choice [ EConst <$> const
                 , EVar (-1) <$> qidentifier
                 , ESing <$> (char '#' >> atype)
                 , buildNumber <$> number
                 , EStringLit <$> stringLit
                 , parens
                   (do ts <- commaSep1 term
                       case (ts, mapM labeledTerm ts) of
                          ([t], _) -> return t
                          (_, Just (t : ts)) -> return (foldl (\t1 t2 -> EApp (EApp (EConst CConcat) t1) t2) t ts)
                          (_, Nothing) -> unexpected $ Label (fromList "unlabeled term"))
                 ]

  labeledTerm t@(ELabel _ _ _) = Just t
  labeledTerm _                = Nothing

  const = choice [reserved s >> return k | (s, k) <-
                   [("prj", CPrj),
                    ("inj", CInj),
                    ("(++)", CConcat),
                    ("(|)", CBranch),
                    ("syn", CSyn),
                    ("ana", CAna),
                    ("fold", CFold),
                    ("in", CIn),
                    ("out", COut),
                    ("fix", CFix),
                    ("(^)", CStringCat)]]

  buildNumber 0 = EVar (-1) (reverse ["Data", "Nat", "zero"])
  buildNumber n = EApp (EVar (-1) (reverse ["Data", "Nat", "succ"])) (buildNumber (n - 1))

data TL = KindSig Kind | TypeDef Ty | TypeSig Ty | TermDef Term | ImportTL [String]
  deriving (Data, Eq, Show, Typeable)

data LHS = TypeLHS String | TermLHS String | ImportLHS

topLevel :: Parser ([Char], TL)
topLevel = item lhs body where
  lhs = reserved "import" *> return ImportLHS <|>
        TypeLHS <$> lexeme typeIdentifier <|>
        TermLHS <$> identifier
  -- You would imagine that I could write `symbol "type" *> identifier` here.
  -- You would be wrong, because `identifier` is defined in terms of `lexeme`,
  -- which will check the indentation level, but we are looking for entries at
  -- *exactly* the start of the current block.
  --
  -- Maybe this points to a more cunning behavior for lexeme: that having
  -- checked the indentation *once*, nested calls should not check it further.
  typeIdentifier = reserved "type" *> ((:) <$> letterChar <*> many alphaNumChar)
  body ImportLHS   = ("",) . ImportTL <$> commaSep (lexeme (some (alphaNumChar <|> char '.')))
  body (TypeLHS x) = colon *> ((x,) . KindSig <$> kind) <|>
                     symbol "=" *> ((x,) . TypeDef <$> ty)
  body (TermLHS x) = colon *> ((x,) . TypeSig <$> ty) <|>
                     symbol "=" *> ((x,) . TermDef <$> term)

prog :: [String] -> Parser Program
prog moduleNames = whitespace >> block topLevel >>= defns moduleNames

defns :: MonadFail m => [String] -> [(String, TL)] -> m Program
defns moduleNames tls
  -- | not (null unmatchedTermDefs) = fail $ "definitions of " ++ intercalate ", " unmatchedTermDefs ++ " lack type signatures"
  | not (null unmatchedTypeSigs) = fail $ "definitions of " ++ intercalate ", " unmatchedTypeSigs ++ " lack bodies"
  | not (null unmatchedTypeDefs) = fail $ "definitions of types " ++ intercalate ", " unmatchedTypeDefs ++ " lack kind signatures"
  | not (null unmatchedKindSigs) = fail $ "definitions of types " ++ intercalate ", " unmatchedKindSigs ++ " lack bodies"
  | otherwise =
    do ds <- mapM mkDecl names
       return (Prog (concat imports, ds))


    -- return (Prog (concat imports, map mkDecl names))
  where -- TODO: Why would not we *not* traverse this list four times?
        termDefs = [(x, t) | (x, TermDef t) <- tls]
        typeSigs = [(x, t) | (x, TypeSig t) <- tls]
        typeDefs = [(x, t) | (x, TypeDef t) <- tls]
        kindSigs = [(x, t) | (x, KindSig t) <- tls]
        imports  = [names | (_, ImportTL names) <- tls]

        names = go [] tls where
          go seen [] = []
          go seen (("", _) : tls) =
            go seen tls
          go seen ((x, _) : tls)
            | x `elem` seen = go seen tls
            | otherwise = x : go (x : seen) tls

        -- unmatchedTermDefs = filter (`notElem` map fst typeSigs) (map fst termDefs)
        unmatchedTypeSigs = filter (`notElem` map fst termDefs) (map fst typeSigs)
        unmatchedTypeDefs = filter (`notElem` map fst kindSigs) (map fst typeDefs)
        unmatchedKindSigs = filter (`notElem` map fst typeDefs) (map fst kindSigs)

        lookups x = map snd . filter ((x ==) . fst)

        mkDecl x =
          case (lookups x termDefs, lookups x typeSigs, lookups x typeDefs, lookups x kindSigs) of
            (tm : tms, [], [], [])
              | null tms -> return (TmDecl (x : moduleNames) Nothing tm)
              | otherwise -> fail $ "too many definitions for " ++ x
            (tm : tms, ty : tys, [], [])
              | null tms, null tys -> return (TmDecl (x : moduleNames) (Just ty) tm)
              | not (null tms) -> fail $ "too many definitions for " ++ x
              | otherwise -> fail $ "too many type signatures for " ++ x
            ([], [], ty : tys, k : ks)
              | null tys, null ks -> return (TyDecl (x : moduleNames) k ty)
              | not (null tys) -> fail $ "too many definitions for " ++ x
              | otherwise -> fail $ "too many kind signatures for " ++ x
            _ -> fail $ "too much definition of " ++ x

        -- mkDecl x = fromMaybe (error $ "in building declaration of " ++ x) decl where
        --   decl = do tm <- lookup x termDefs
        --             return (TmDecl (x : moduleNames) (lookup x typeSigs) tm)
        --          `mplus`
        --          do k <- lookup x kindSigs
        --             ty <- lookup x typeDefs
        --             return (TyDecl (x : moduleNames) k ty)

parse :: String -> [String] -> String -> IO Program
parse fileName moduleNames s =
  do let tls = evalState (runParserT (prog moduleNames <* eof) fileName s) []
     case tls of
       Left err -> do hPutStrLn stderr (errorBundlePretty err)
                      exitFailure
       Right tls -> return tls