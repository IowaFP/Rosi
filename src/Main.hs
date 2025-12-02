{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Main where

import Control.Monad ((<=<), void, when)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State
import Data.IORef
import Data.List (findIndex, break)
import Data.List.Split
import Data.Bitraversable
import qualified Prettyprinter as P
import qualified Prettyprinter.Util as P
import System.Console.GetOpt
import System.Exit (exitFailure)
import System.Directory
import System.Environment
import System.FilePath
import System.IO (hPutStrLn, stderr, stdout, hSetBuffering, BufferMode(..))

import Checker
import Interp.Erased as E
import Parser
import Printer
import Scope
import Syntax

-- data Flag = Eval String | Input String | Import String | TraceKindInference
--           | TraceTypeInference | TraceEvaluation | PrintTypedTerms | PrintOkay | Reset
--   deriving Show

data Flags = Flags { evals :: [String], inputs :: [String], imports :: [String]
                   , doTraceKindInference, doTraceInference
                   , doTraceEvaluation, doPrintTyped, printOkay
                   , doPrintKinds, doPrintMaps :: Bool }

emptyFlags :: Flags
emptyFlags = Flags [] [] [] False False False False False False False

-- interpretFlag :: Flags -> Flag -> Flags
-- interpretFlag f (Eval s)           = f { evals = evals f ++ splitOn "," s }
-- interpretFlag f (Input s)          = f { inputs = inputs f ++ [s] }
-- interpretFlag f (Import s)         = f { imports = imports f ++ [s] }
-- interpretFlag f PrintOkay          = f { printOkay = True }
-- interpretFlag f TraceKindInference = f { doTraceKindInference = True }
-- interpretFlag f TraceTypeInference = f { doTraceInference = True }
-- interpretFlag f TraceEvaluation    = f { doTraceEvaluation = True }
-- interpretFlag f PrintTypedTerms    = f { doPrintTyped = True }
-- interpretFlag f Reset              = Flags [] [] [] False False False False False False False

interpretFlags = foldl (flip ($)) emptyFlags

options :: [OptDescr (Flags -> Flags)]
options = [ Option ['e'] ["eval"] (ReqArg (\s f -> f { evals = evals f ++ splitOn "," s}) "SYMBOL") "symbol to evaluate"
          , Option ['i'] ["import"] (ReqArg (\s f -> f { imports = imports f ++ [s]}) "DIR") "directory to search"
          , Option [] [] (ReqArg (\s f -> f { inputs = inputs f ++ [s]}) "FILE") "file to process"
          , Option ['t'] [] (NoArg (\f -> f { doPrintTyped = True })) "print typed terms"
          , Option [] ["okay"] (NoArg (\f -> f { printOkay = True })) "print okay after execution"
          , Option ['K'] ["trace-kind-inference"] (NoArg (\f -> f { doTraceKindInference = True })) "generate trace output in kind inference"
          , Option ['T'] ["trace-type-inference"] (NoArg (\f -> f { doTraceInference = True })) "generate trace output in type inference"
          , Option ['E'] ["trace-evaluation"] (NoArg (\f -> f { doTraceEvaluation = True })) "generate trace output from evaluation"
          , Option [] ["print-kinds"] (NoArg (\f -> f { doPrintKinds = True })) "print kind information"
          , Option [] ["print-maps"] (NoArg (\f -> f { doPrintMaps = True })) "print maps explicitly"
          , Option [] ["reset"] (NoArg (const emptyFlags)) "reset flags" ]
unprog (Prog ds) = ds

parseChasing :: [FilePath] -> [FilePath] -> IO [Decl]
parseChasing additionalImportDirs fs =
  do fs' <- mapM findStartingPoint fs
     evalStateT (chase fs') [] where

  chase :: [([String], FilePath)] -> StateT [FilePath] IO [Decl]
  chase [] = return []
  chase ((moduleName, fn) : fns) =
    do already <- get
       if fn `elem` already
       then chase fns
       else do (imports, decls) <- unprog <$> liftIO (parse fn moduleName =<< readFile fn)
               importFns <- mapM (liftIO . findImport) imports
               imported <- chase importFns
               modify (\already -> fn : already)
               ((imported ++ decls) ++) <$> chase fns

  findImport :: String -> IO ([String], FilePath)
  findImport s = check importDirs
    where moduleName = splitOn "." s
          fn = foldr1 (</>) moduleName <.> "ro"
          importDirs = "." : additionalImportDirs
          check (d : ds) =
            do exists <- doesPathExist (d </> fn)
               if exists then return (reverse moduleName, d </> fn) else check ds
          check [] =
            do hPutStrLn stderr $ "import not found: " ++ s
               exitFailure

  findStartingPoint :: String -> IO ([String], FilePath)
  findStartingPoint s
    | takeExtension s == ".ro" = return ([takeBaseName s], s)
    | otherwise                = findImport s

main :: IO ()
main = do nowArgs <- getArgs
          configFile <- ("." ++) . dropExtension <$> getProgName
          globalArgs <- wordsIfExists =<< getXdgDirectory XdgConfig configFile
          localArgs <- wordsIfExists configFile
          flags <-
             case getOpt (ReturnInOrder (\s f -> f { inputs = inputs f ++ [s]})) options (globalArgs ++ localArgs ++ nowArgs) of
               (flags, [], []) -> return (interpretFlags flags)
               (_, _, errs) -> do hPutStrLn stderr (concat errs)
                                  exitFailure
          writeIORef traceKindInference (doTraceKindInference flags)
          writeIORef traceTypeInference (doTraceInference flags)
          writeIORef E.traceEvaluation (doTraceEvaluation flags)
          when (doTraceInference flags || doTraceEvaluation flags) $
            hSetBuffering stdout LineBuffering
          decls <- parseChasing (imports flags) (inputs flags)
          scoped <- reportErrors $ runScopeM $ scopeProg decls
          checked <- goCheck [] [] scoped
          when (doPrintTyped flags) $
            mapM_ (putDocWLn 120 . pprTyping) checked
          evaled <- goEvalE [] checked
          let output = filter ((`elem` evals flags) . head . fst) evaled
          sequence_ [putStrLn $ stringFromQName x ++ " = " ++ show v | (x, v) <- output]
          when (printOkay flags) $ putStrLn "okay"
  where goCheck d g [] = return []
        goCheck d g (TyDecl x k t : ds) =
          do t' <- flattenT =<< reportErrors =<< runCheckM' d g (typeErrorContext (ErrContextDefn x . ErrContextType t) $ checkTy t k)
             goCheck (KBDefn k t' : d) g ds
        goCheck d g (TmDecl v (Just ty) te : ds) =
          do ty' <- flattenT =<< reportErrors =<< runCheckM' d g (typeErrorContext (ErrContextDefn v . ErrContextType ty) $ fst <$> (normalize [] =<< checkTy ty KType))
             te' <- flattenE =<< reportErrors =<< runCheckM' d g (typeErrorContext (ErrContextDefn v . ErrContextTerm te) $ fst <$> checkTop te (Just ty'))
             ds' <- goCheck d (ty' : g) ds
             return ((v, ty', te') : ds')
        goCheck d g (TmDecl v Nothing te : ds) =
          do (te', ty) <- bitraverse flattenE flattenT =<< reportErrors =<< runCheckM' d g (typeErrorContext (ErrContextDefn v . ErrContextTerm te) $ checkTop te Nothing)
             ds' <- goCheck d (ty : g) ds
             return ((v, ty, te') : ds')
        goCheck d g (TyDecl {} : ds) =
          goCheck d g ds

        goEvalE _ [] = return []
        goEvalE h ((x, t, m) : ds) =
          do m' <- flattenE m
             let v = E.eval ([], h) m'
             ((x, v) :) <$> goEvalE (v : h) ds

        thirdM f (a, b, c) = (a, b,) <$> f c

        wordsIfExists :: FilePath -> IO [String]
        wordsIfExists fn =
          do exists <- doesFileExist fn
             if exists then words <$> readFile fn else return []

reportErrors :: Either Error t -> IO t
reportErrors (Left err) =
  do putDocWLn 80 (pprTypeError err)
     exitFailure
reportErrors (Right x) = return x

putDocWLn :: Int -> RDoc ann -> IO ()
putDocWLn n d = do P.putDocW n =<< runReaderT d (PO {level = 0, printKinds = False, printMaps = False})
                   putStrLn ""