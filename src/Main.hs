{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Main where

import Control.Monad (void)
import Control.Monad.Except (withError)
import Control.Monad.Reader (runReaderT)
import qualified Data.Map as M
import qualified Prettyprinter as P
import qualified Prettyprinter.Util as P
import System.Console.GetOpt
import System.Exit (exitFailure)
import System.FilePath
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)

import Agda
import Checker
import Naive
import Parser
import Printer
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
          checked <- go [] decls 
          let h@(E (_, he)) = E (M.empty, M.fromList [(v, eval h te') | (v, _, te') <- checked])
          -- mapM_ (putDocWLn 80) [pprTyDecl x ty | (x, ty, _) <- checked]
          mapM_ (putDocWLn 120) [pprBinding v e | (v, e) <- M.toList he, v `elem` evals]
  where go g [] = return []
        go g (Decl (v, ty, te) : ds) =
          do ty' <- flattenT =<< reportErrors =<< runCheckM (withError (ErrContextType ty) $ checkTy ty KType)
             te' <- flattenE =<< reportErrors =<< runCheckM' g (withError (ErrContextTerm te) $ checkTerm te ty')
             ds' <- go ((v, ty') : g) ds
             return ((v, ty', te') : ds')

reportErrors :: Either TypeError t -> IO t
reportErrors (Left err) =
  do putDocWLn 80 (pprTypeError err)
     exitFailure
reportErrors (Right x) = return x

putDocWLn :: Int -> RDoc ann -> IO ()
putDocWLn n d = do P.putDocW n =<< runReaderT d (PO {level = 0, printKinds = False})
                   putStrLn ""