{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Main where

import Control.Monad (void)
import Control.Monad.Except (withError)
import Control.Monad.Reader (runReaderT)
import Data.List (findIndex)
import qualified Prettyprinter as P
import qualified Prettyprinter.Util as P
import System.Console.GetOpt
import System.Exit (exitFailure)
import System.FilePath
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)

import Checker
import Naive
import Parser
import Printer
import Scope
import Syntax

data Flag = Eval String | Input String
  deriving Show

splitFlags :: [Flag] -> ([String], [String])
splitFlags [] = ([], [])
splitFlags (Eval s : fs) = (s : evals, files)
  where (evals, files) = splitFlags fs
splitFlags (Input s : fs) = (evals, s : files)
  where (evals, files) = splitFlags fs

options :: [OptDescr Flag]
options = [ Option ['e'] ["eval"] (ReqArg Eval "SYMBOL") "symbol to evaluate"
          , Option ['i'] ["input"] (ReqArg Input "FILE") "input file" ]

unprog (Prog ds) = ds

main :: IO ()
main = do args <- getArgs
          (evals, files) <-
             case getOpt (ReturnInOrder Input) options args of
               (flags, [], []) -> return (splitFlags flags)
               (_, _, errs) -> do hPutStrLn stderr (concat errs)
                                  exitFailure
          decls <- concatMap unprog <$> mapM (\fn -> parse fn =<< readFile fn) files
          scoped <- reportErrors $ runScopeM $ scopeProg decls
          checked <- goCheck [] scoped 
          let evaled = goEval [] checked
              output = filter ((`elem` evals) . fst) evaled
          mapM_ (putDocWLn 120 . uncurry pprBinding) output
  where goCheck g [] = return []
        goCheck g (Decl (v, ty, te) : ds) =
          do ty' <- flattenT =<< reportErrors =<< runCheckM (withError (ErrContextType ty) $ checkTy ty KType)
             te' <- flattenE =<< reportErrors =<< runCheckM' g (withError (ErrContextTerm te) $ checkTop te ty')
             ds' <- goCheck (ty' : g) ds
             return ((v, ty', te') : ds')

        goEval _ [] = []
        goEval h ((x, t, m) : ds) = (x, v) : goEval (v : h) ds where 
          v = eval (E ([], h)) m 

reportErrors :: Either Error t -> IO t
reportErrors (Left err) =
  do putDocWLn 80 (pprTypeError err)
     exitFailure
reportErrors (Right x) = return x

putDocWLn :: Int -> RDoc ann -> IO ()
putDocWLn n d = do P.putDocW n =<< runReaderT d (PO {level = 0, printKinds = False})
                   putStrLn ""