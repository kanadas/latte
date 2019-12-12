module Main where


import System.IO
import System.Environment ( getArgs {-, getProgName -})
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)
--import Control.Monad.Trans.Reader
--import Control.Monad.State.Lazy
--import Control.Monad.Except
import qualified Data.Map.Strict as Map

import LexLatte
import ParLatte
import PrintLatte
import AbsLatte
import Frontend

import ErrM

type ParseFun a = [Token] -> Err a

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrV v f >> readFile f >>= run v p

run :: Verbosity -> ParseFun Program -> String -> IO ()
run v p s = let ts = myLexer s in case p ts of
    Bad err -> do 
        hPutStrLn stderr "ERROR"
        putStrLn "Parse Failed:"
        putStrV v "Tokens:"
        putStrV v $ show ts
        putStrLn $ err ++ "\n"
        exitFailure
    Ok program -> case runCheckProgram program of
        Right _ -> hPutStrLn stderr "OK" >> exitSuccess
        Left exc -> hPutStrLn stderr "ERROR" >> putStrLn "Semantic check failed:" >> putStrLn (show exc) >> exitFailure

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -v (files)      Verbose mode. Parse content of files verbosely."
    ]
  exitFailure

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--help"] -> usage
        [] -> getContents >>= run 0 pProgram
        "-v":fs -> mapM_ (runFile 2 pProgram) fs
        fs -> mapM_ (runFile 0 pProgram) fs

