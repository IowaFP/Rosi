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
import Interp.Naive as N
import Parser
import Printer
import Scope
import Syntax

data Flag = Eval String | Input String | Import String | UseNaiveInterpreter | TraceKindInference
          | TraceTypeInference | TraceEvaluation | PrintTypedTerms | PrintOkay | Reset
  deriving Show

data Flags = Flags { evals :: [String], inputs :: [String], imports :: [String]
                   , useNaiveInterpreter, doTraceKindInference, doTraceInference
                   , doTraceEvaluation, doPrintTyped, printOkay :: Bool }

interpretFlag :: Flags -> Flag -> Flags
interpretFlag f (Eval s)           = f { evals = evals f ++ splitOn "," s }
interpretFlag f (Input s)          = f { inputs = inputs f ++ [s] }
interpretFlag f (Import s)         = f { imports = imports f ++ [s] }
interpretFlag f UseNaiveInterpreter = f { useNaiveInterpreter = True }
interpretFlag f PrintOkay          = f { printOkay = True }
interpretFlag f TraceKindInference = f { doTraceKindInference = True }
interpretFlag f TraceTypeInference = f { doTraceInference = True }
interpretFlag f TraceEvaluation    = f { doTraceEvaluation = True }
interpretFlag f PrintTypedTerms    = f { doPrintTyped = True }
interpretFlag f Reset              = Flags [] [] [] False False False False False False

interpretFlags = foldl interpretFlag (Flags [] [] [] False False False False False False)

options :: [OptDescr Flag]
options = [ Option ['e'] ["eval"] (ReqArg Eval "SYMBOL") "symbol to evaluate"
          , Option ['i'] ["import"] (ReqArg Import "DIR") "directory to search"
          , Option [] [] (ReqArg Input "FILE") "file to process"
          , Option ['t'] [] (NoArg PrintTypedTerms) "print typed terms"
          , Option [] ["okay"] (NoArg PrintOkay) "print okay after execution"
          , Option ['N'] ["naive"] (NoArg UseNaiveInterpreter) "use naive interpreter"
          , Option ['K'] ["trace-kind-inference"] (NoArg TraceKindInference) "generate trace output in kind inference"
          , Option ['T'] ["trace-type-inference"] (NoArg TraceTypeInference) "generate trace output in type inference"
          , Option ['E'] ["trace-evaluation"] (NoArg TraceEvaluation) "generate trace output from evaluation"
          , Option [] ["reset"] (NoArg Reset) "reset flags" ]
unprog (Prog ds) = ds

parseChasing :: [FilePath] -> [FilePath] -> IO [Decl]
parseChasing additionalImportDirs fs =
  do fs' <- mapM findStartingPoint fs
     evalStateT (chase fs') [] where

  chase :: [FilePath] -> StateT [FilePath] IO [Decl]
  chase [] = return []
  chase (fn : fns) =
    do already <- get
       if fn `elem` already
       then chase fns
       else do (imports, decls) <- unprog <$> liftIO (parse fn =<< readFile fn)
               importFns <- mapM (liftIO . findImport) imports
               imported <- chase importFns
               modify (\already -> fn : already)
               ((imported ++ decls) ++) <$> chase fns

  findImport :: String -> IO FilePath
  findImport s = check importDirs
    where fn = foldr1 (</>) (splitOn "." s) <.> "ro"
          importDirs = "." : additionalImportDirs
          check (d : ds) =
            do exists <- doesPathExist (d </> fn)
               if exists then return (d </> fn) else check ds
          check [] =
            do hPutStrLn stderr $ "import not found: " ++ s
               exitFailure

  findStartingPoint :: String -> IO FilePath
  findStartingPoint s
    | takeExtension s == ".ro" = return s
    | otherwise                = findImport s

main :: IO ()
main = do nowArgs <- getArgs
          configFile <- ("." ++) . dropExtension <$> getProgName
          globalArgs <- wordsIfExists =<< getXdgDirectory XdgConfig configFile
          localArgs <- wordsIfExists configFile
          flags <-
             case getOpt (ReturnInOrder Input) options (globalArgs ++ localArgs ++ nowArgs) of
               (flags, [], []) -> return (interpretFlags flags)
               (_, _, errs) -> do hPutStrLn stderr (concat errs)
                                  exitFailure
          writeIORef traceKindInference (doTraceKindInference flags)
          writeIORef traceTypeInference (doTraceInference flags)
          writeIORef N.traceEvaluation (doTraceEvaluation flags)
          writeIORef E.traceEvaluation (doTraceEvaluation flags)
          when (doTraceInference flags || doTraceEvaluation flags) $
            hSetBuffering stdout LineBuffering
          decls <- parseChasing (imports flags) (inputs flags)
          scoped <- reportErrors $ runScopeM $ scopeProg decls
          checked <- goCheck [] [] scoped
          when (doPrintTyped flags) $
            mapM_ (putDocWLn 120 . pprTyping) checked
          if useNaiveInterpreter flags
          then do evaled <- goEvalN [] checked
                  let output = filter ((`elem` evals flags) . fst) evaled
                  mapM_ (putDocWLn 120 . uncurry pprBinding) output
          else do evaled <- goEvalE [] checked
                  let output = filter ((`elem` evals flags) . fst) evaled
                  sequence_ [putStrLn $ x ++ " = " ++ show v | (x, v) <- output]
          when (printOkay flags) $ putStrLn "okay"
  where goCheck d g [] = return []
        goCheck d g (TyDecl x k t : ds) =
          do t' <- flattenT =<< reportErrors =<< runCheckM' d g (errorContext (ErrContextDefn x . ErrContextType t) $ checkTy t k)
             goCheck (KBDefn k t' : d) g ds
        goCheck d g (TmDecl v (Just ty) te : ds) =
          do ty' <- flattenT =<< reportErrors =<< runCheckM' d g (errorContext (ErrContextDefn v . ErrContextType ty) $ fst <$> (normalize [] =<< checkTy ty KType))
             te' <- flattenE =<< reportErrors =<< runCheckM' d g (errorContext (ErrContextDefn v . ErrContextTerm te) $ fst <$> checkTop te (Just ty'))
             ds' <- goCheck d (ty' : g) ds
             return ((v, ty', te') : ds')
        goCheck d g (TmDecl v Nothing te : ds) =
          do (te', ty) <- bitraverse flattenE flattenT =<< reportErrors =<< runCheckM' d g (errorContext (ErrContextDefn v . ErrContextTerm te) $ checkTop te Nothing)
             ds' <- goCheck d (ty : g) ds
             return ((v, ty, te') : ds')
        goCheck d g (TyDecl {} : ds) =
          goCheck d g ds

        goEvalN _ [] = return []
        goEvalN h ((x, t, m) : ds) =
          do m' <- flattenE m
             let v = N.eval (E ([], h)) m'
             ((x, v) :) <$> goEvalN (v : h) ds

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
putDocWLn n d = do P.putDocW n =<< runReaderT d (PO {level = 0, printKinds = False})
                   putStrLn ""