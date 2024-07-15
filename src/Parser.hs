module Parser where

import Syntax

import Control.Monad (foldM, replicateM)
import Control.Monad.IO.Class
import Data.Char (isSpace)
import Data.IORef
import Data.List (intercalate)
import Text.Parsec hiding (parse)
import Text.Parsec.Language
import qualified Text.Parsec.Token as P


--------------------------------------------------------------------------------
-- Lexer


-- Copy and paste to change the monad... fix me!

-- | The language definition for the language Haskell98.

haskellStyleIO :: P.GenLanguageDef String u IO
haskellStyleIO = P.LanguageDef
                { P.commentStart   = "{-"
                , P.commentEnd     = "-}"
                , P.commentLine    = "--"
                , P.nestedComments = True
                , P.identStart     = letter
                , P.identLetter    = alphaNum <|> oneOf "_'"
                , P.opStart        = P.opLetter haskellStyleIO
                , P.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , P.reservedOpNames= []
                , P.reservedNames  = []
                , P.caseSensitive  = True
                }                

roLanguage :: P.GenLanguageDef String u IO
roLanguage  = haskellStyleIO

roParser   :: P.GenTokenParser String u IO
roParser    = P.makeTokenParser roLanguage

lexeme      = P.lexeme roParser
identifier  = P.identifier roParser
reserved    = P.reserved roParser
operator    = P.operator roParser
reservedOp  = P.reservedOp roParser
natural     = P.natural roParser
symbol      = P.symbol roParser
parens      = P.parens roParser
angles      = P.angles roParser -- Don't think I need this...
brackets    = P.brackets roParser
braces      = P.braces roParser
semi        = P.semi roParser
comma       = P.comma roParser
colon       = P.colon roParser
dot         = P.dot roParser
semiSep     = P.semiSep roParser
semiSep1    = P.semiSep1 roParser
commaSep    = P.commaSep roParser
commaSep1   = P.commaSep1 roParser

terminal p = do x <- p
                notFollowedBy anyToken
                return x

ps p = runParserT p () ""

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

type Parser = ParsecT String () IO

kind :: Parser Kind
kind = chainr1 akind (reservedOp "->" >> return KFun) where
  akind =  choice [ reserved "*" >> return KType
                  , reserved "L" >> return KLabel
                  , parens kind
                  , do reserved "R"
                       KRow <$> brackets kind ]

binders :: Parser t -> (Goal t -> IO t) -> Parser [(String, t)]
binders p unif = 
  do xs <- many1 identifier
     m <- optionMaybe $ do colon >> p
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
             [ do reservedOp "\\"
                  bs <- commaSep1 (binders kind (return . KUnif))
                  dot
                  return (foldr (\(v, k) f -> TLam v k . f) id (concat bs))
             , do reserved "forall"
                  bs <- commaSep1 (binders kind (return . KUnif))
                  dot
                  return (foldr (\(v, k) f -> TForall v k . f) id (concat bs)) ]  

  thenTy :: Parser Ty
  thenTy = scan where
    scan :: Parser Ty
    scan = tyOrP >>= rest

    rest (Right t) = return t
    rest (Left ps)  = do reservedOp "=>"
                         t <- scan
                         return (foldr TThen t ps)
                    <|>
                      unexpected "predicate"

tyOrP :: Parser (Either [Pred] Ty)  
tyOrP = Left <$> try (commaSep1 pr) <|> Right <$> arrTy

arrTy :: Parser Ty
arrTy = chainr1 appTy (reservedOp "->" >> return (\t u -> TApp (TApp TFun t) u)) where

appTy = do t <- atype
           choice 
             [ do reservedOp ":="
                  (u : us) <- many1 atype
                  return (TLabeled t (foldl TApp u us))
             , do us <- many atype
                  return (foldl TApp t us) ]
labeledTy = 
  do t <- appTy
     case t of
       TLabeled _ _ -> return t
       _ -> unexpected "unlabeled type"

atype :: Parser Ty
atype = choice [ TLab <$> (lexeme (char '\'' >> many1 (letter <|> digit)))
               , TSing <$> (char '#' >> atype)
               , TSigma <$> (reserved "Sigma" >> atype)
               , TPi <$> (reserved "Pi" >> atype)
               , TRow <$> (braces (commaSep labeledTy))
               , flip TVar Nothing <$> identifier
               , parens ty ]

pr :: Parser Pred
pr = do t <- arrTy
        choice
          [ do reservedOp "<"
               PLeq t <$> arrTy
          , do reservedOp "+"
               u <- arrTy
               reservedOp "~"
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
  prefix = do reservedOp "\\" 
              bs <- commaSep1 (binders ty (\g -> return (TUnif g KType)))
              dot
              return (foldr1 (.) (map (uncurry ELam) (concat bs)))
         <|>
           do reservedOp "/\\"
              bs <- commaSep1 (binders kind (return . KUnif))
              dot
              return (foldr1 (.) (map (uncurry ETyLam) (concat bs)))

  op s k = reservedOp s >> k

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
appTerm = do (t : ts) <- many1 (BuiltIn <$> builtIns <|> Type <$> brackets ty <|> Term <$> aterm)
             app t ts where
  app (Term t) [] = return t
  app (Type _) _ = unexpected "type argument"
  app (BuiltIn s) [] = unexpected ("unsaturated " ++ s)
  app _ (BuiltIn s : _) = unexpected s
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
  app (BuiltIn s) _ = unexpected ("ill-formed" ++ s)

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
    builtIn s = reserved s >> return s

  aterm = choice [ EVar <$> identifier
                 , ESing <$> (char '#' >> atype)
                 , ELab <$> (lexeme (char '\'' >> many1 (letter <|> digit)))
                 , parens term ]
  
topLevel = 
  do x <- identifier
     choice 
       [ do colon
            (x,) . Left <$> ty
       , do reservedOp "="
            (x,) . Right <$> term ]          

defns :: [(String, Either Ty Term)] -> IO Program
defns tls
  | not (null unmatchedTerms) = fail $ "definitions of " ++ intercalate ", " unmatchedTerms ++ " lack type signatures"
  | not (null unmatchedTypes) = fail $ "definitions of " ++ intercalate ", " unmatchedTypes ++ " lack bodies"
  | otherwise = return (Prog [Decl (x, ty, te) | (x, ty) <- typeMap, let (Just te) = lookup x termMap])
  where termMap = [(x, t) | (x, Right t) <- tls]
        typeMap = [(x, t) | (x, Left t) <- tls]
        unmatchedTerms = filter (`notElem` map fst typeMap) (map fst termMap)
        unmatchedTypes = filter (`notElem` map fst termMap) (map fst typeMap)
        
parse :: String -> IO Program
parse s = do tls <- sequence <$> mapM (runParserT topLevel () "") ss
             case tls of
               Left err -> fail (show err)
               Right tls -> defns tls
  where ss = topLevels s
