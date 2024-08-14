module Parser where

import Syntax

import Control.Monad (foldM, replicateM, void, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State
import Data.Char (isSpace)
import Data.IORef (newIORef)
import Data.List (intercalate)
import Data.List.NonEmpty (fromList)
import Data.Void (Void)
import System.IO (hPutStrLn, stderr) 
import System.Exit (exitFailure)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as P
import Text.Megaparsec.Error

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

ps p s = evalStateT (runParserT p "" s) []

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

item :: Parser a -> Parser b -> (a -> b -> c) -> Parser c
item p q f = 
  do here <- P.indentLevel
     x <- p
     pushIndent GT here
     f x <$> q <* popIndent

at goal p = 
  do here <- P.indentLevel
     when (here /= goal) (P.incorrectIndent EQ goal here)
     p 

block :: Parser a -> Parser [a]
block p =
  do here <- P.indentLevel
     pushIndent EQ here
     many p <* popIndent

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

-- This is dumb, but avoids thinking
--
-- Actually, this also messes up line numbers, so it really needs fixed...

topLevels :: String -> [String]
topLevels = reverse . foldr combine [] . reverse . lines where
  combine s ts'@(~(t : ts))
    | all isSpace s = ts'
    | take 2 (dropWhile isSpace s) == "--" = ts'
    | isSpace (head s) = (t ++ '\n': s) : ts
    | otherwise = s : ts'

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
ty = do pfs <- many prefix
        ty <- thenTy
        return (foldr ($) ty pfs) where
  prefix :: Parser (Ty -> Ty)          
  prefix = choice 
             [ do symbol "\\"
                  bs <- commaSep1 (binders kind (return . KUnif))
                  dot
                  return (foldr (\(v, k) f -> TLam v k . f) id (concat bs))
             , do symbol "forall"
                  bs <- commaSep1 (binders kind (return . KUnif))
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
arrTy = chainr1 appTy (symbol "->" >> return (\t u -> TApp (TApp TFun t) u)) where

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
atype = choice [ TLab <$> (lexeme (char '\'' >> some alphaNumChar))
               , TSing <$> (char '#' >> atype)
               , TSigma <$> (symbol "Sigma" >> atype)
               , TPi <$> (symbol "Pi" >> atype)
               , TRow <$> (braces (commaSep labeledTy))
               , flip TVar Nothing <$> identifier
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
--     ++ ? ++m ?m
--     := / 

term :: Parser Term
term = do ps <- many prefix
          t <- branchTerm 
          return (foldr ($) t ps) where

  prefix :: Parser (Term -> Term)
  prefix = do symbol "\\" 
              bs <- commaSep1 (binders ty (\g -> return (TUnif g KType)))
              dot
              return (foldr1 (.) (map (uncurry ELam) (concat bs)))
         <|>
           do symbol "/\\"
              bs <- commaSep1 (binders kind (return . KUnif))
              dot
              return (foldr1 (.) (map (uncurry ETyLam) (concat bs)))

  op s k = symbol s >> k

  branchTerm = chainl1 labTerm $ choice [op "++" (ebinary EConcat) , op "?" (ebinary EBranch)] where
    ebinary k = liftIO $ 
                do [rx, ry, rz] <- replicateM 3 (newIORef Nothing)
                   vx <- newIORef Nothing
                   kx <- newIORef Nothing
                   let rk = KRow (KUnif (Goal ("k$e", kx)))
                   return $ k (TUnif (Goal ("t$x", rx)) rk) (TUnif (Goal ("t$y", ry)) rk) (TUnif (Goal ("t$z", rz)) rk) (VGoal (Goal ("v$x", vx)))

  labTerm = chainl1 appTerm $ choice [op ":=" (return ELabeled), op "/" (return EUnlabel)]

data AppTerm = BuiltIn String | Type Ty | Term Term

appTerm :: Parser Term
appTerm = do (t : ts) <- some (BuiltIn <$> builtIns <|> Type <$> brackets ty <|> Term <$> aterm)
             app t ts where
  app (Term t) [] = return t
  app (Type _) _ = unexpected (Label $ fromList "type argument")
  app (BuiltIn s) [] = unexpected (Label $ fromList ("unsaturated " ++ s))
  app _ (BuiltIn s : _) = unexpected (Label $ fromList s)
  app (Term t) (Term u : ts) = app (Term (EApp t u)) ts
  app (Term t) (Type u : ts) = app (Term (ETyApp t u)) ts
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
  app (BuiltIn "ana") (Term t : ts) = app (Term (EAna (TLam "X" KType (TVar "X" (Just KType))) t)) ts
  app (BuiltIn "syn") (Type phi : Term t : ts) = app (Term (ESyn phi t)) ts
  app (BuiltIn "syn") (Term t : ts) = app (Term (ESyn (TLam "X" KType (TVar "X" (Just KType))) t)) ts
  app (BuiltIn s) _ = unexpected (Label $ fromList ("ill-formed " ++ s))

  goal s = Goal . (s,) <$> newIORef Nothing

  unary k mty mtz t = 
    liftIO $ 
    do ke <- KUnif <$> goal "k$e"
       ty <- maybe (TUnif <$> goal "t$y" <*> pure (KRow ke)) return mty
       tz <- maybe (TUnif <$> goal "t$z" <*> pure (KRow ke)) return mtz
       g  <- VGoal <$> goal "v$plus"
       return (k ty tz g t)

  binary k mtx mty mtz t u =
    liftIO $ 
    do ke <- KUnif <$> goal "k$e"
       tx <- maybe (TUnif <$> goal "t$x" <*> pure (KRow ke)) return mtx
       ty <- maybe (TUnif <$> goal "t$y" <*> pure (KRow ke)) return mty
       tz <- maybe (TUnif <$> goal "t$z" <*> pure (KRow ke)) return mtz
       g  <- VGoal <$> goal "v$plus"
       return (k tx ty tz g t u)

  builtIns = choice (map builtIn ["prj", "inj", "ana", "syn", "(++)", "(?)"]) where
    builtIn s = symbol s >> return s

  aterm = choice [ EVar <$> identifier
                 , ESing <$> (char '#' >> atype)
                 , ELab <$> lexeme (char '\'' >> some alphaNumChar)
                 , parens term ]
  
topLevel = item identifier (colon *> (Left <$> ty) <|> symbol "=" *> (Right <$> term)) (,)

prog :: Parser Program
prog = whitespace >> block topLevel >>= liftIO . defns

-- topLevel = 
--   do x <- identifier
--      choice 
--        [ do colon
--             (x,) . Left <$> ty
--        , do symbol "="
--             (x,) . Right <$> term ]          

defns :: [(String, Either Ty Term)] -> IO Program
defns tls
  | not (null unmatchedTerms) = fail $ "definitions of " ++ intercalate ", " unmatchedTerms ++ " lack type signatures"
  | not (null unmatchedTypes) = fail $ "definitions of " ++ intercalate ", " unmatchedTypes ++ " lack bodies"
  | otherwise = return (Prog [Decl (x, ty, te) | (x, ty) <- typeMap, let (Just te) = lookup x termMap])
  where termMap = [(x, t) | (x, Right t) <- tls]
        typeMap = [(x, t) | (x, Left t) <- tls]
        unmatchedTerms = filter (`notElem` map fst typeMap) (map fst termMap)
        unmatchedTypes = filter (`notElem` map fst termMap) (map fst typeMap)
        
parse :: String -> String -> IO Program
parse fn s = 
  do tls <- evalStateT (runParserT prog fn s) []
     case tls of
       Left err -> do hPutStrLn stderr (errorBundlePretty err)
                      exitFailure
       Right tls -> return tls