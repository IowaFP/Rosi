{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Main where

import Control.Monad ((<=<), void, when)
import Control.Monad.Except (withError)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State
import Data.IORef
import Data.List (findIndex, break)
import Data.List.Split
import qualified Prettyprinter as P
import qualified Prettyprinter.Util as P
import System.Console.GetOpt
import System.Exit (exitFailure)
import System.Directory
import System.FilePath
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)

import Checker
import Naive
import Parser
import Printer
import Scope
import Syntax

data Flag = Eval String | Input String | Import String | TraceTypeInference | PrintTypedTerms
  deriving Show

data Flags = Flags { evals :: [String], inputs :: [String], imports :: [String], doTrace :: Bool, doPrintTyped :: Bool }


splitFlags :: [Flag] -> Flags
splitFlags [] = Flags [] [] [] False False
splitFlags (Eval s : fs) = f { evals = ss ++ evals f}
  where f = splitFlags fs
        ss = split ',' s
        split c s = go (dropWhile (c ==) s) where
          go [] = []
          go s  = s' : go (dropWhile (c ==) s'') where
            (s', s'') = break (c ==) s
splitFlags (Input s : fs) = f { inputs = s : inputs f }
  where f = splitFlags fs
splitFlags (Import s : fs) = f { imports = s : imports f }
  where f = splitFlags fs
splitFlags (TraceTypeInference : fs) = f { doTrace = True }
  where f = splitFlags fs
splitFlags (PrintTypedTerms : fs) = f { doPrintTyped = True }
  where f = splitFlags fs

options :: [OptDescr Flag]
options = [ Option ['e'] ["eval"] (ReqArg Eval "SYMBOL") "symbol to evaluate"
          , Option ['i'] ["import"] (ReqArg Import "DIR") "directory to search"
          , Option [] [] (ReqArg Input "FILE") "file to process"
          , Option ['t'] [] (NoArg PrintTypedTerms) "print typed terms"
          , Option ['T'] ["trace-type-inference"] (NoArg TraceTypeInference) "generate trace output in type inference" ]

unprog (Prog ds) = ds

parseChasing :: [FilePath] -> [FilePath] -> IO [Decl]
parseChasing additionalImportDirs fs = evalStateT (chase fs) [] where

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

main :: IO ()
main = do args <- getArgs
          flags <-
             case getOpt (ReturnInOrder Input) options args of
               (flags, [], []) -> return (splitFlags flags)
               (_, _, errs) -> do hPutStrLn stderr (concat errs)
                                  exitFailure
          writeIORef traceTypeInference (doTrace flags)
          decls <- parseChasing (imports flags) (inputs flags)
          scoped <- reportErrors $ runScopeM $ scopeProg decls
          checked <- goCheck [] [] scoped
          when (doPrintTyped flags) $
            mapM_ ((putDocWLn 120 . pprTyping) <=< thirdM flattenE) checked
          evaled <- goEval [] checked
          let output = filter ((`elem` evals flags) . fst) evaled
          mapM_ (putDocWLn 120 . uncurry pprBinding) output
          putStrLn "ok"
  where goCheck d g [] = return []
        goCheck d g (TyDecl x k t : ds) =
          do t' <- flattenT =<< reportErrors =<< runCheckM' d g (withError (ErrContextType t) $ checkTy t k)
             goCheck ((k, Just t') : d) g ds
        goCheck d g (TmDecl v ty te : ds) =
          do ty' <- flattenT =<< reportErrors =<< runCheckM' d g (withError (ErrContextType ty) $ fst <$> (normalize =<< checkTy ty KType))
             te' <- flattenE =<< reportErrors =<< runCheckM' d g (withError (ErrContextTerm te) $ checkTop te ty')
             ds' <- goCheck d (ty' : g) ds
             return ((v, ty', te') : ds')
        goCheck d g (TyDecl {} : ds) =
          goCheck d g ds

        goEval _ [] = return []
        goEval h ((x, t, m) : ds) =
          do m' <- flattenE m
             let v = eval (E ([], h)) m'
             ((x, v) :) <$> goEval (v : h) ds

        thirdM f (a, b, c) = (a, b,) <$> f c

reportErrors :: Either Error t -> IO t
reportErrors (Left err) =
  do putDocWLn 80 (pprTypeError err)
     exitFailure
reportErrors (Right x) = return x

putDocWLn :: Int -> RDoc ann -> IO ()
putDocWLn n d = do P.putDocW n =<< runReaderT d (PO {level = 0, printKinds = False})
                   putStrLn ""