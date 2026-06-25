{-# LANGUAGE DeriveDataTypeable #-}
{- HLINT ignore "Fuse foldr/map" -}
module Parser where

import Syntax

import Control.Monad              (foldM, guard, mplus, replicateM, void, when)
import Control.Monad.Reader
import Control.Monad.State

import Data.Char                  (isSpace)
import Data.Data                  hiding (Fixity, Infix, Prefix)
import Data.Functor
import Data.IORef                 (newIORef)
import Data.List                  (delete, find, intercalate, singleton)
import Data.List.NonEmpty         (fromList)
import Data.List.Split            (splitOn)
import Data.Maybe                 (fromMaybe, isNothing)
import Data.Void                  (Void)
import System.Exit                (exitFailure)
import System.IO                  (hPutStrLn, stderr)

import Text.Megaparsec            hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as P
import Text.Megaparsec.Error

import Checker.Monad              (bind)
import Data.Map                   (fromAscList)
import Debug.Trace                qualified as T
import Text.Megaparsec.Debug      (dbg)


--------------------------------------------------------------------------------
-- Combinators I miss from Parsec

terminal p = p <* eof

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op =
  do lhs <- p
     rhss <- many (do f <- op
                      rhs <- p
                      return (f, rhs))
     return (down lhs rhss)
  where down lhs []                 = lhs
        down lhs ((op, rhs) : rhss) = op lhs (down rhs rhss)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op =
  do lhs <- p
     rhss <- many (do f <- op
                      rhs <- p
                      return (f, rhs))
     return (down lhs rhss)
  where down lhs []                 = lhs
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
       []    -> return Nothing
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


     x y z. M

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
reserved s  = lexeme (try (string s <* notFollowedBy (alphaNumChar <|> char '\'' <|> char '_')))

identifier  =
  do s <- ((:) <$> letterChar <*> many (alphaNumChar <|> char '\'' <|> char '_'))
     if s `elem` keywords
     then unexpected $ Label (fromList "reserved word")
     else return s
  where keywords = ["let", "in", "forall", "infixl", "infixr", "infix", "prefix", "postfix", "__Apply"]

lidentifier :: Parser String
lidentifier =
  char '\'' >> some (alphaNumChar <|> char '\'' <|> char '_')

qidentifier  =
  do xs <- many (try (identifier <* string "." <* notFollowedBy (string "\'" <|> string "#")))
     x <- try identifier <|> try surroundedOp
     return (x:reverse xs)


-- TODO(mctano) centralize source of truth for reserved keywords and operators
customOperator :: ParsecT Void [Char] (State [(Ordering, Pos)]) [Char]
customOperator =
  do
    s <- takeWhile1P (Just "operator symbol")
                     -- we support all operator symbols supported by Idris 2 ( ":+-*\\/=.?|&><!@$%^~#" ) except for '.', '#', and '@'
                     -- See (https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html#data-types)
                     (`elem` ":+-*\\/=?|&><!$%^~")
                     -- alternate symbol set based on the `isSymbol` class. May be more trouble than it's worth.
                     --  (\c -> (isSymbol c || c `elem` "-*\\/?&!%") && c /= '`')
    if s `elem` reserved
      then unexpected $ Label (fromList "reserved operator")
      else return s
  where
    reserved = [":", "++", "|", "^", "~", "@", "/", ":=", "=", "->", "#"]


immediateParens = between (char '(') (char ')')
immediateBackticks = between (char '`') (char '`')
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

number      = P.decimal
stringLit   = lexeme (char '"' >> manyTill P.charLiteral (char '"'))

surroundedOp = immediateParens customOperator
surroundedQIdentifier = immediateBackticks qidentifier
surroundedIdentifier = immediateBackticks identifier


---------------------------------------------------------------------------------
-- Parser

kind :: Parser Kind
kind = chainr1 akind (symbol "->" >> return KFun) where
  akind =  choice [ symbol "*" >> return KType
                  , symbol "L" >> return KLabel
                  , parens kind
                  , do symbol "R"
                       KRow <$> brackets kind ]

typeLamBinders :: Parser [(String, Maybe Kind)]
typeLamBinders =
  choice
    [ singleton . (, Nothing) <$> lexeme identifier
    , parens $ do xs <- some (lexeme identifier)
                  k <- colon >> kind
                  return (map (, Just k) xs) ]

ty :: Parser Ty
ty = do pfs <- many prefix
        ty <- thenTy
        return (foldr ($) ty pfs) where

  quantBinders :: Parser [(String, Maybe Kind)]
  quantBinders =
    do xs <- some (lexeme identifier)
       m <- optional $ do colon >> kind
       return (map (, m) xs)

  prefix :: Parser (Ty -> Ty)
  prefix = choice
             [ do symbol "\\"
                  bs <- some typeLamBinders
                  dot
                  return (foldr (\(v, k) f -> TLam v k . f) id (concat bs))
             , do reserved "forall"
                  bs <- commaSep1 quantBinders
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
minusTy =
    chainl1 (apps <$> some mapType)
            (choice [ lexeme (try (string "-" <* notFollowedBy (char '>'))) *> return TCompl  -- wtf is this?
                    , symbol "+" *> return TPlus
                    ])

apps :: [Ty] -> Ty
apps = foldl1 TApp

mapType :: Parser Ty
mapType =
  do t <- atype
     us <- many (symbol "*")
     return (foldr (const TMap) t us)

labeledTy =
  do t <- labTy
     case t of
       TLabeled _ _ -> return t
       _            -> unexpected (Label $ fromList "unlabeled type")


tcon = choice [ ordered (string "Pi") Pi
              , ordered (string "Sigma") Sigma
              , symbol "Mu" >> return (TConApp (Mu Unexpanded)) ] where
  ordered p k =
    lexeme $
    do p
       choice
         [ try (char '<') >> return (TConOrd k Leq)
         , try (char '>') >> return (TConOrd k Geq)
         , return (TConApp k) ]

atype :: Parser Ty
atype = choice [ TLab <$> lexeme lidentifier
               , TSing <$> (char '#' >> atype)
               , tcon <*> atype
               , TRow <$> braces (commaSep labeledTy)
               , const TString <$> reserved "String"
               , TVar (-1) <$> (lexeme qidentifier)
               , parens ty ]

pr :: Parser Pred
pr = choice [ do reserved "Fold"
                 PFold <$> arrTy
            , do t <- arrTy
                 choice
                   [ do reserved "<"
                        PLeq t <$> arrTy
                  , do reserved "~"
                       u <- arrTy
                       return $ case t of
                         TPlus x y -> PPlus x y u
                         _         -> PEq t u ] ]

-- We need a random precedence table here.  Let's try:
--
--     ++ ?
--     := /

termLamBinders :: Parser [Either (String, Maybe Kind) (String, Maybe Ty)]
termLamBinders =
  choice
    [ singleton . Right . (, Nothing) <$> try (lexeme (try identifier <|> surroundedOp))
    , singleton . Left  . (, Nothing) <$> lexeme (char '@' >> identifier)
    , try $ parens $ do xs <- some (try (lexeme (try identifier <|> surroundedOp)))
                        t <- colon >> ty
                        return (map (Right . (, Just t)) xs)
    , parens $ do xs <- some (lexeme (char '@' >> identifier))
                  t <- colon >> kind
                  return (map (Left . (, Just t)) xs)
    ]


term :: Parser Term
term = prefixes typedTerm where

  prefix :: Parser (Term -> Term)
  prefix = do symbol "\\"
              bs <- some termLamBinders
              dot
              return (foldr1 (.) (map (either (uncurry ETyLam) (uncurry ELam)) (concat bs)))
         <|>
           do symbol "let"
              x <- lexeme identifier
              mty <- optional $ symbol ":" >> ty
              symbol "="
              t <- term
              symbol "in"
              let t' = maybe t (ETyped t) mty
              return (ELet x t')

  prefixes :: Parser Term -> Parser Term
  prefixes rest =
    do mp <- optional (try prefix)
       case mp of
         Nothing -> rest
         Just f  -> f <$> prefixes rest

  op :: String -> Parser a -> Parser a
  op s k = symbol s >> k

  typedTerm :: Parser Term
  typedTerm =
    do t <- branchTerm
       maybe t (ETyped t) <$> optional (symbol ":" >> ty)

  ebinary :: Const -> Parser (Term -> Term -> Term)
  ebinary k = return (\e1 e2 -> EApp (EApp (EConst k) e1) e2)

  branchTerm = chainl1 caseTerm $ choice [op "++" (ebinary CConcat) , op "|" (ebinary CBranch)]

  caseTerm =
        do p <- try (pattern <* symbol "->")
           buildCase p <$> caseTerm
    <|> do try (symbol "otherwise" >> symbol "->")
           EApp (EVar (-1) (reverse ["Ro", "Base", "otherwise"])) <$> caseTerm
    <|> composeTerm
    where
    pattern =
      do k <- choice [ ESing . TLab <$> lidentifier
                     , EVar (-1) <$> qidentifier ]
         symbol ":"
         x <- lexeme identifier
         return (k, x)

    -- case ,k (\,x. ,t)
    buildCase (k, x) t =
      EApp
        (EApp (EVar (-1) (reverse ["Ro", "Base", "case"]))
              k)
        (ELam x Nothing t)

  -- ELam "x" Nothing (EApp e1 (EApp e2 (EVar 0 ["x"])))
  o :: Term
  o = ELam "f" Nothing
     (ELam "g" Nothing
     (ELam "x" Nothing
       (EApp (EVar (-1) ["f"])
         (EApp (EVar (-1) ["g"]) (EVar (-1) ["x"])))))

  composeTerm :: Parser Term
  composeTerm = chainr1 labTerm (op "." (return (\ e1 e2 -> EApp (EApp o e1) e2)))

  labTerm :: Parser Term
  labTerm =
    do t <- stringEqTerm
       choice
         [ do symbol ":="
              ELabel Nothing t <$> term
         , do symbol "/"
              EUnlabel Nothing t <$> stringEqTerm
         , return t ]

  stringEqTerm = chainl1 catTerm $ op "~" (ebinary CStringEq)

  catTerm = chainl1 infixExpr $ op "^" (ebinary CStringCat)

  infixExpr =  eliminateTrivial . EInfix . concat <$> some (try appTerm <|> try (singleton . flip (Operator (-1)) Nothing <$> lexeme (try (singleton <$> customOperator) <|> surroundedQIdentifier)))
    where
          -- Not everything needs to be an EInfix.
          eliminateTrivial (EInfix [Operand tm]) = tm
          eliminateTrivial                     e = e


data AppTerm = Type Ty | Term Term | Op String

appTerm :: Parser [EInfixToken]
appTerm = do (t : ts) <- some (Type <$> (char '@' >> atype) <|> Term <$> aterm)
             app (t:ts) where

  app :: [AppTerm] -> Parser [EInfixToken]
  app [Term t]             = return [Operand t]
  app (Type _:_)           = unexpected (Label $ fromList "type argument")
  app (Term t:Term u : ts) = (Operand t:) . (explicitApp:) <$> app (Term u:ts)

  app (Term t:Type u : ts) = app (Term (EInst t (Known [TyArg u])):ts)

  goal s = Goal . (s,) <$> newIORef Nothing

  ctor = do x <- choice [ ESing . TLab <$> lidentifier
                        , EVar (-1) <$> qidentifier ]
            char ':'
            notFollowedBy (char '=')
            return (EApp (EVar (-1) (reverse ["Ro", "Base", "con"])) x)

  sing x = [x]
  buildSel x l = EApp (EApp (EVar (-1) (reverse ["Ro", "Base", "sel"])) x) l

  selection =
    do x <- EVar (-1) <$> qidentifier
       xs <- many $ do char '.'
                       choice [ ESing . TLab <$> lidentifier
                              , EVar (-1) . sing <$> identifier]
       return (foldl buildSel x xs)

  stor =
    do xs <- some $ do char '.'
                       choice [ ESing . TLab <$> lidentifier
                              , EVar (-1) . sing <$> identifier]
       return (ELam "$x" Nothing (foldl buildSel (EVar (-1) ["$x"]) xs))

  aterm :: Parser Term
  aterm = choice [ EConst <$> const
                 , try (lexeme ctor)
                 , try (lexeme selection)
                 , try (lexeme stor)
                 , lexeme $ do char '?'
                               name <- many (alphaNumChar <|> char '\'' <|> char '_')
                               return (EHole name)
                 , ESing . TLab <$> lexeme lidentifier
                 , EVar (-1) <$> try (lexeme qidentifier)
                 , ESing <$> (char '#' >> atype)
                 , buildNumber <$> lexeme number
                 , EStringLit <$> stringLit
                 , do symbol "("
                      t <- do ts <- commaSep term
                              case (ts, mapM labeledTerm ts) of
                                 ([], _)            -> return (EVar (-1) (reverse ["Ro", "Base", "tt"]))
                                 ([t], _)           -> return t
                                 (_, Just (t : ts)) -> return (foldl (\t1 t2 -> EApp (EApp (EConst CConcat) t1) t2) t ts)
                                 (_, Nothing)       -> unexpected $ Label (fromList "unlabeled term")
                      guardIndent (string ")")
                      s <- optional stor
                      whitespace
                      return $ maybe t (`EApp` t) s
                 ]

  labeledTerm :: Term -> Maybe Term
  labeledTerm t@(ELabel _ _ _) = Just t
  labeledTerm _                = Nothing

  const :: Parser Const
  const = choice [reserved s >> return k | (s, k) <-
                   [("prj", CPrj),
                    ("inj", CInj),
                    ("(++)", CConcat),
                    ("(|)", CBranch),
                    ("syn", CSyn),
                    ("ana", CAna),
                    ("fold", CFold),
                    ("fix", CFix),
                    ("(^)", CStringCat),
                    ("(~)", CStringEq)]]

  buildNumber :: Int -> Term
  buildNumber 0 = EVar (-1) (reverse ["Data", "Nat", "zero"])
  buildNumber n = EApp (EVar (-1) (reverse ["Data", "Nat", "succ"])) (buildNumber (n - 1))

data TL = KindSig Kind | TypeDef Ty | TypeSig Ty | TermDef Term | ImportTL [String] | FixityDecl Fixity
  deriving (Data, Eq, Show, Typeable)

data LHS = TypeLHS String | TermLHS String | ImportLHS | FixityLHS FixityKeyword
  deriving (Show)

topLevel :: Parser ([Char], TL)
topLevel = item lhs body where
  lhs = choice
          [ try $ ImportLHS <$ reserved "import"
          , try $ TypeLHS <$> lexeme typeIdentifier
          , try $ TermLHS <$> try (lexeme (try identifier <|> surroundedOp))
          , try $ FixityLHS <$> lexeme fixityKeyword
          ]
  -- You would imagine that I could write `symbol "type" *> identifier` here.
  -- You would be wrong, because `identifier` is defined in terms of `lexeme`,
  -- which will check the indentation level, but we are looking for entries at
  -- *exactly* the start of the current block.
  --
  -- Maybe this points to a more cunning behavior for lexeme: that having
  -- checked the indentation *once*, nested calls should not check it further.

  fixityKeyword :: Parser FixityKeyword
  fixityKeyword = choice
    [ try $ InfixL <$ reserved "infixl"
    , try $ InfixR <$ reserved "infixr"
    , try $ Infix  <$ reserved "infix"
    , try $ Prefix <$ reserved "prefix"
    ,      Postfix <$ reserved "postfix"
    ]

  typeIdentifier = reserved "type" *> ((:) <$> letterChar <*> many (alphaNumChar <|> char '\'' <|> char '_'))
  body ImportLHS   = ("",) . ImportTL <$> commaSep (lexeme (some (alphaNumChar <|> char '.')))
  body (TypeLHS x) =
    choice
      [ colon *> ((x,) . KindSig <$> kind)
      , do bs <- many typeLamBinders
           let binders = foldr (.) id (map (uncurry TLam) (concat bs))
           symbol "=" *> ((x,) . TypeDef . binders <$> ty) ]
  body (TermLHS x) =
    choice
      [ colon *> ((x,) . TypeSig <$> ty)
      , do bs <- many termLamBinders
           let binders = foldr (.) id (map (either (uncurry ETyLam) (uncurry ELam)) (concat bs))
           symbol "=" *> ((x,) . TermDef . binders <$> term) ]
  body (FixityLHS fx) = do lvl <- lexeme number
                           name <- lexeme (try customOperator <|> surroundedIdentifier)
                           return (name, FixityDecl (Fixity fx lvl))


prog :: [String] -> Parser Program
prog moduleNames = whitespace >> block topLevel >>= defns moduleNames

defns :: MonadFail m => [String] -> [(String, TL)] -> m Program
defns moduleNames tls
  | not (null unmatchedTypeSigs) = fail $ "definitions of " ++ intercalate ", " unmatchedTypeSigs ++ " lack bodies"
  | not (null unmatchedTypeDefs) = fail $ "definitions of types " ++ intercalate ", " unmatchedTypeDefs ++ " lack kind signatures"
  | not (null unmatchedKindSigs) = fail $ "definitions of types " ++ intercalate ", " unmatchedKindSigs ++ " lack bodies"
  | not (null unmatchedFixDecls) = fail $ moduleName ++ " contains fixity declaration(s) for [ " ++ intercalate ", " unmatchedFixDecls ++ " ] without definition(s) in the same module."
  | otherwise =
    do ds <- mapM mkDecl names
       let
       return (Prog (concat imports, ds))
  where -- TODO: Why would not we *not* traverse this list four times?
        termDefs = [(x, t) | (x, TermDef t) <- tls]
        typeSigs = [(x, t) | (x, TypeSig t) <- tls]
        typeDefs = [(x, t) | (x, TypeDef t) <- tls]
        kindSigs = [(x, t) | (x, KindSig t) <- tls]

        -- hey, why not five times?
        -- Get the fixity declarations for each name.
        fixDecls = [(x, fixity) | (x, FixityDecl fixity) <- tls]

        imports  = [names | (_, ImportTL names) <- tls]


        names = go [] tls where
          go seen [] = []
          go seen (("", _) : tls) =
            go seen tls
          -- skip fixity declarations so we don't get scope errors later.
          go seen ((x, FixityDecl _) : tls) = go seen tls
          go seen ((x, _) : tls)
            | x `elem` seen = go seen tls
            | otherwise = x : go (x : seen) tls

        -- unmatchedTermDefs = filter (`notElem` map fst typeSigs) (map fst termDefs)
        unmatchedTypeSigs = filter (`notElem` map fst termDefs) (map fst typeSigs)
        unmatchedTypeDefs = filter (`notElem` map fst kindSigs) (map fst typeDefs)
        unmatchedKindSigs = filter (`notElem` map fst typeDefs) (map fst kindSigs)
        unmatchedFixDecls = filter (`notElem` map fst termDefs) (map fst fixDecls)

        lookups x = map snd . filter ((x ==) . fst)
        mkDecl x =
          do fx <- case lookups x fixDecls of
                        [] -> return Nothing
                        (fx:fxs) | null fxs -> return (Just fx)
                                 | otherwise -> fail $ "too many fixity declarations for " ++ x ++ " in " ++ moduleName
             case (lookups x termDefs, lookups x typeSigs, lookups x typeDefs, lookups x kindSigs, fx) of
                  (tm : tms, [], [], [], fx)
                    -- TODO(mctano) If fixity declaration and type both exist, check that they match
                    -- i.e. unary op is `A -> B`, binary op is `A -> B -> C`
                    | null tms -> return (TmDecl (x : moduleNames) Nothing tm fx)
                    | otherwise -> fail $ "too many definitions for " ++ x
                  (tm : tms, ty : tys, [], [], fx)
                    -- TODO(mctano) If fixity declaration and type both exist, check that they match
                    | null tms, null tys -> return (TmDecl (x : moduleNames) (Just ty) tm fx)
                    | not (null tms) -> fail $ "too many definitions for " ++ x
                    | otherwise -> fail $ "too many type signatures for " ++ x
                  ([], [], ty : tys, k : ks, _)
                    | null tys, null ks -> return (TyDecl (x : moduleNames) k ty)
                    | not (null tys) -> fail $ "too many definitions for " ++ x
                    | otherwise -> fail $ "too many kind signatures for " ++ x
                  ([], [], [], [], _) -> fail $ "no definition for " ++ x
                  r -> fail $ "too much definition of " ++ x

        moduleName = intercalate "." (reverse moduleNames)




parse :: String -> [String] -> String -> IO Program
parse fileName moduleNames s =
  do let tls = evalState (runParserT (prog moduleNames <* eof) fileName s) []
     case tls of
       Left err -> do hPutStrLn stderr (errorBundlePretty err)
                      exitFailure
       Right tls -> return tls
