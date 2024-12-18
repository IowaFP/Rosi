{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Main where

import Control.Monad (void)
import Control.Monad.Except (withError)
import Control.Monad.Reader (runReaderT)
import Data.IORef
import Data.List (findIndex, break)
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

data Flag = Eval String | Input String | TraceTypeInference
  deriving Show

splitFlags :: [Flag] -> ([String], [String], Bool)
splitFlags [] = ([], [], False)
splitFlags (Eval s : fs) = (ss ++ evals, files, b)
  where (evals, files, b) = splitFlags fs
        ss = split ',' s
        split c s = go (dropWhile (c ==) s) where
          go [] = []
          go s  = s' : go (dropWhile (c ==) s'') where
            (s', s'') = break (c ==) s          
splitFlags (Input s : fs) = (evals, s : files, b)
  where (evals, files, b) = splitFlags fs
splitFlags (TraceTypeInference : fs) = (evals, files, True)
  where (evals, files, _) = splitFlags fs

options :: [OptDescr Flag]
options = [ Option ['e'] ["eval"] (ReqArg Eval "SYMBOL") "symbol to evaluate"
          , Option ['i'] ["input"] (ReqArg Input "FILE") "input file" 
          , Option ['T'] ["trace-type-inference"] (NoArg TraceTypeInference) "generate trace output in type inference" ]

unprog (Prog ds) = ds

main :: IO ()
main = do args <- getArgs
          (evals, files, traceTI) <-
             case getOpt (ReturnInOrder Input) options args of
               (flags, [], []) -> return (splitFlags flags)
               (_, _, errs) -> do hPutStrLn stderr (concat errs)
                                  exitFailure
          writeIORef traceTypeInference traceTI
          decls <- concatMap unprog <$> mapM (\fn -> parse fn =<< readFile fn) files
          scoped <- reportErrors $ runScopeM $ scopeProg decls
          checked <- goCheck [] [] scoped 
          let evaled = goEval [] checked
              output = filter ((`elem` evals) . fst) evaled
          mapM_ (putDocWLn 120 . uncurry pprBinding) output
          putStrLn "ok"
  where goCheck d g [] = return []
        goCheck d g (TyDecl x k t : ds) = 
          do t' <- flattenT =<< reportErrors =<< runCheckM' d g (withError (ErrContextType t) $ checkTy t k)
             goCheck ((k, Just t') : d) g ds
        goCheck d g (TmDecl v ty te : ds) =
          do ty' <- flattenT =<< reportErrors =<< runCheckM' d g (withError (ErrContextType ty) $ checkTy ty KType)
             te' <- flattenE =<< reportErrors =<< runCheckM' d g (withError (ErrContextTerm te) $ checkTop te ty')
             ds' <- goCheck d (ty' : g) ds
             return ((v, ty', te') : ds')
        goCheck d g (TyDecl {} : ds) =
          goCheck d g ds

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