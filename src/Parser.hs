{-# LANGUAGE DeriveDataTypeable #-}
module Parser where

import Syntax

import Control.Monad (foldM, mplus, replicateM, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader
import Control.Monad.State

import Data.Char (isSpace)
import Data.Data
import Data.IORef (newIORef)
import Data.List (delete, intercalate)
import Data.List.NonEmpty (fromList)
import Data.Maybe (fromMaybe)
import Data.Void (Void)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import Text.Megaparsec
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

ps p s = putStrLn . either errorBundlePretty show =<< runReaderT (evalStateT (runParserT p "" s) []) ([], [])

--------------------------------------------------------------------------------

type Parser = ParsecT Void [Char] (StateT [(Ordering, Pos)] IO)

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
identifier  = lexeme ((:) <$> letterChar <*> many alphaNumChar)
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

---------------------------------------------------------------------------------
-- Parser

kind :: Parser Kind
kind = chainr1 akind (symbol "->" >> return KFun) where
  akind =  choice [ symbol "*" >> return KType
                  , symbol "L" >> return KLabel
                  , parens kind
                  , do symbol "R"
                       KRow <$> brackets kind ]

binders :: Parser t -> (Goal t -> IO t) -> Parser [(String, t)]
binders p unif =
  do xs <- some identifier
     m <- optional $ do colon >> p
     case m of
       Just t -> return [(x, t) | x <- xs]
       Nothing -> mapM (\x -> do r <- liftIO $ newIORef Nothing
                                 t <- liftIO $ unif (Goal ("g$" ++ x, r))
                                 return (x, t)) xs

ty :: Parser Ty
ty = do (xss, pfs) <- unzip <$> many prefix
        ty <- thenTy
        return (foldr ($) ty pfs) where
  prefix :: Parser ([String], Ty -> Ty)
  prefix = choice
             [ do symbol "\\"
                  bs <- commaSep1 (binders kind (return . KUnif))
                  dot
                  return (fst <$> concat bs, foldr (\(v, k) f -> TLam v k . f) id (concat bs))
             , do symbol "forall"
                  bs <- commaSep1 (binders kind (return . KUnif))
                  dot
                  return (fst <$> concat bs, foldr (\(v, k) f -> TForall v k . f) id (concat bs)) ]

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
arrTy = chainr1 appTy (symbol "->" >> return (\t u -> TApp (TApp TFun t) u))

appTy = do t <- atype
           choice
             [ do symbol ":="
                  (u : us) <- some atype
                  return (TLabeled t (foldl TApp u us))
             , do us <- many atype
                  return (foldl TApp t us) ]
labeledTy =
  do t <- appTy
     case t of
       TLabeled _ _ -> return t
       _ -> unexpected (Label $ fromList "unlabeled type")

atype :: Parser Ty
atype = choice [ TLab <$> lexeme (char '\'' >> some alphaNumChar)
               , TSing <$> (char '#' >> atype)
               , TSigma <$> (symbol "Sigma" >> atype)
               , TPi <$> (symbol "Pi" >> atype)
               , TRow <$> braces (commaSep labeledTy)
               , flip (TVar (-1)) Nothing <$> identifier
               , parens ty ]

pr :: Parser Pred
pr = do t <- arrTy
        choice
          [ do symbol "<"
               PLeq t <$> arrTy
          , do symbol "+"
               u <- arrTy
               symbol "~"
               PPlus t u <$> arrTy ]

-- We need a random precedence table here.  Let's try:
--
--     ++ ?
--     := /

term :: Parser Term
term = prefixes typedTerm where

  prefix :: Parser (([String], [String]), Term -> Term) -- now this `Term -> Term` trick is really not paying off any longer...
  prefix = do symbol "\\"
              bs <- commaSep1 (binders ty (\g -> return (TUnif 0 0 g KType)))
              dot
              return (([], fst <$> concat bs), foldr1 (.) (map (uncurry ELam) (concat bs)))
         <|>
           do symbol "/\\"
              bs <- commaSep1 (binders kind (return . KUnif))
              dot
              return ((fst <$> concat bs, []), foldr1 (.) (map (uncurry ETyLam) (concat bs)))

  prefixes :: Parser Term -> Parser Term
  prefixes rest =
    do mp <- optional (try prefix)
       case mp of
         Nothing -> rest
         Just (bs, f) -> f <$> prefixes rest

  op s k = symbol s >> k

  typedTerm =
    do t <- branchTerm
       maybe t (ETyped t) <$> optional (symbol ":" >> ty)

  branchTerm = chainl1 labTerm $ choice [op "++" (ebinary EConcat) , op "?" (ebinary EBranch)] where
    ebinary k = liftIO $
                do [rx, ry, rz] <- replicateM 3 (newIORef Nothing)
                   vx <- newIORef Nothing
                   kx <- newIORef Nothing
                   let rk = KRow (KUnif (Goal ("k$e", kx)))
                   return $ k (TUnif 0 0 (Goal ("t$x", rx)) rk) (TUnif 0 0 (Goal ("t$y", ry)) rk) (TUnif 0 0 (Goal ("t$z", rz)) rk) (VGoal (Goal ("v$x", vx)))

  labTerm = chainl1 appTerm $ choice [op ":=" (return ELabel), op "/" (return EUnlabel)]

data AppTerm = BuiltIn String | Type Ty | Term Term

appTerm :: Parser Term
appTerm = do (t : ts) <- some (BuiltIn <$> builtIns <|> Type <$> brackets ty <|> Term <$> aterm)
             app t ts where
  app (Term t) [] = return t
  app (Type _) _ = unexpected (Label $ fromList "type argument")
  app (BuiltIn s) [] = unexpected (Label $ fromList ("unsaturated " ++ s))
  app _ (BuiltIn s : _) = unexpected (Label $ fromList s)
  app (Term t) (Term u : ts) = app (Term (EApp t u)) ts
  app (Term t) (Type u : ts) = app (Term (EInst t (Known [TyArg u]))) ts
  app (BuiltIn "prj") (Term t : ts) =
    do prjt <- unary EPrj Nothing Nothing t
       app (Term prjt) ts
  app (BuiltIn "prj") (Type y : Term t : ts) =
    do prjt <- unary EPrj (Just y) Nothing t
       app (Term prjt) ts
  app (BuiltIn "prj") (Type y : Type z : Term t : ts) =
    do prjt <- unary EPrj (Just y) (Just z) t
       app (Term prjt) ts
  app (BuiltIn "inj") (Term t : ts) =
    do injt <- unary EInj Nothing Nothing t
       app (Term injt) ts
  app (BuiltIn "inj") (Type y : Term t : ts) =
    do injt <- unary EInj (Just y) Nothing t
       app (Term injt) ts
  app (BuiltIn "inj") (Type y : Type z : Term t : ts) =
    do injt <- unary EInj (Just y) (Just z) t
       app (Term injt) ts
  app (BuiltIn "(++)") (Term t : Term u : ts) =
    do catt <- binary EConcat Nothing Nothing Nothing t u
       app (Term catt) ts
  app (BuiltIn "(++)") (Type x : Term t : Term u : ts) =
    do catt <- binary EConcat (Just x) Nothing Nothing t u
       app (Term catt) ts
  app (BuiltIn "(++)") (Type x : Type y : Term t : Term u : ts) =
    do catt <- binary EConcat (Just x) (Just y) Nothing t u
       app (Term catt) ts
  app (BuiltIn "(++)") (Type x : Type y : Type z : Term t : Term u : ts) =
    do catt <- binary EConcat (Just x) (Just y) (Just z) t u
       app (Term catt) ts
  app (BuiltIn "(?)") (Term t : Term u : ts) =
    do brnt <- binary EBranch Nothing Nothing Nothing t u
       app (Term brnt) ts
  app (BuiltIn "(?)") (Type x : Term t : Term u : ts) =
    do brnt <- binary EBranch (Just x) Nothing Nothing t u
       app (Term brnt) ts
  app (BuiltIn "(?)") (Type x : Type y : Term t : Term u : ts) =
    do brnt <- binary EBranch (Just x) (Just y) Nothing t u
       app (Term brnt) ts
  app (BuiltIn "(?)") (Type x : Type y : Type z : Term t : Term u : ts) =
    do brnt <- binary EBranch (Just x) (Just y) (Just z) t u
       app (Term brnt) ts
  app (BuiltIn "ana") (Type phi : Term t : ts) = app (Term (EAna phi t)) ts
  app (BuiltIn "ana") (Term t : ts) = app (Term (EAna (TLam "X" KType (TVar 0 "X" (Just KType))) t)) ts
  app (BuiltIn "syn") (Type phi : Term t : ts) = app (Term (ESyn phi t)) ts
  app (BuiltIn "syn") (Term t : ts) = app (Term (ESyn (TLam "X" KType (TVar 0 "X" (Just KType))) t)) ts
  app (BuiltIn s) _ = unexpected (Label $ fromList ("ill-formed " ++ s))

  goal s = Goal . (s,) <$> newIORef Nothing

  unary k mty mtz t =
    liftIO $
    do ke <- KUnif <$> goal "k$e"
       ty <- maybe (TUnif 0 0 <$> goal "t$y" <*> pure (KRow ke)) return mty
       tz <- maybe (TUnif 0 0 <$> goal "t$z" <*> pure (KRow ke)) return mtz
       g  <- VGoal <$> goal "v$plus"
       return (k ty tz g t)

  binary k mtx mty mtz t u =
    liftIO $
    do ke <- KUnif <$> goal "k$e"
       tx <- maybe (TUnif 0 0 <$> goal "t$x" <*> pure (KRow ke)) return mtx
       ty <- maybe (TUnif 0 0 <$> goal "t$y" <*> pure (KRow ke)) return mty
       tz <- maybe (TUnif 0 0 <$> goal "t$z" <*> pure (KRow ke)) return mtz
       g  <- VGoal <$> goal "v$plus"
       return (k tx ty tz g t u)

  builtIns = choice (map builtIn ["prj", "inj", "ana", "syn", "(++)", "(?)"]) where
    builtIn s = symbol s >> return s

  aterm = choice [ EVar (-1) <$> identifier
                 , ESing <$> (char '#' >> atype)
                 , parens term ]

data TL = KindSig Kind | TypeDef Ty | TypeSig Ty | TermDef Term
  deriving (Data, Eq, Show, Typeable)

topLevel :: Parser ([Char], TL)
topLevel = item lhs body where
  lhs = Left <$> lexeme typeIdentifier <|>
        Right <$> identifier
  -- You would imagine that I could write `symbol "type" *> identifier` here.
  -- You would be wrong, because `identifier` is defined in terms of `lexeme`,
  -- which will check the identation level, but we are looking for entries at
  -- *exactly* the start of the current block.
  --
  -- Maybe this points to a more cunning behavior for lexeme: that having
  -- checked the indentation *once*, nested calls should not check it further.
  typeIdentifier = symbol "type" *> ((:) <$> letterChar <*> many alphaNumChar)
  body (Left x)  = colon *> ((x,) . KindSig <$> kind) <|>
                   symbol "=" *> ((x,) . TypeDef <$> ty)
  body (Right x) = colon *> ((x,) . TypeSig <$> ty) <|>
                   symbol "=" *> ((x,) . TermDef <$> term)

prog :: Parser Program
prog = whitespace >> block topLevel >>= defns

defns :: MonadFail m => [(String, TL)] -> m Program
defns tls
  | not (null unmatchedTermDefs) = fail $ "definitions of " ++ intercalate ", " unmatchedTermDefs ++ " lack type signatures"
  | not (null unmatchedTypeSigs) = fail $ "definitions of " ++ intercalate ", " unmatchedTypeSigs ++ " lack bodies"
  | not (null unmatchedTypeDefs) = fail $ "definitions of types " ++ intercalate ", " unmatchedTypeDefs ++ " lack kind signatures"
  | not (null unmatchedKindSigs) = fail $ "definitions of types " ++ intercalate ", " unmatchedKindSigs ++ " lack bodies"
  | otherwise = return (Prog (map mkDecl names))
  where -- TODO: Why would not we *not* traverse this list four times?
        termDefs = [(x, t) | (x, TermDef t) <- tls]
        typeSigs = [(x, t) | (x, TypeSig t) <- tls]
        typeDefs = [(x, t) | (x, TypeDef t) <- tls]
        kindSigs = [(x, t) | (x, KindSig t) <- tls]

        names = go [] tls where
          go seen [] = []
          go seen ((x, _) : tls)
            | x `elem` seen = go seen tls
            | otherwise = x : go (x : seen) tls

        unmatchedTermDefs = filter (`notElem` map fst typeSigs) (map fst termDefs)
        unmatchedTypeSigs = filter (`notElem` map fst termDefs) (map fst typeSigs)
        unmatchedTypeDefs = filter (`notElem` map fst kindSigs) (map fst typeDefs)
        unmatchedKindSigs = filter (`notElem` map fst typeDefs) (map fst kindSigs)

        mkDecl x = fromMaybe (error $ "in building declaration of " ++ x) decl where
          decl = do ty <- lookup x typeSigs
                    tm <- lookup x termDefs
                    return (TmDecl x ty tm)
                 `mplus`
                 do k <- lookup x kindSigs
                    ty <- lookup x typeDefs
                    return (TyDecl x k ty)

parse :: String -> String -> IO Program
parse fn s =
  do tls <- evalStateT (runParserT (prog <* eof) fn s) []
     case tls of
       Left err -> do hPutStrLn stderr (errorBundlePretty err)
                      exitFailure
       Right tls -> return tls