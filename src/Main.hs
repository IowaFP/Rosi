module Main where

import System.Exit (exitFailure)
import System.FilePath
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)


import Agda
import Checker
import Parser
import Syntax

unprog (Prog ds) = ds

main :: IO ()
main = do files <- getArgs
          decls <- concatMap unprog <$> mapM (\fn -> parse fn =<< readFile fn) files
          go [] decls where
  go g [] = return ()
  go g (Decl (v, ty, te) : ds) =
    do putStrLn (v ++ ":")
       ty' <- flattenT =<< reportErrors =<< runCheckM (checkTy ty KType)
       putStrLn (show ty')
       te' <- flattenE =<< reportErrors =<< runCheckM' g (checkTerm te ty')
       putStrLn (show te')
       go ((v, ty') : g) ds

reportErrors :: Either String t -> IO t
reportErrors (Left err) =
  do hPutStrLn stderr (unlines ["error:", err])
     exitFailure
reportErrors (Right x) = return x  