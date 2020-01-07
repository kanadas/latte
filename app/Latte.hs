module Main where


import System.IO
import System.Environment ( getArgs {-, getProgName -})
import System.Exit ( exitFailure, exitSuccess )
import System.FilePath
import System.Process
import Control.Monad (when)
import Data.List
--import Control.Monad.Trans.Reader
--import Control.Monad.State.Lazy
--import Control.Monad.Except
--import qualified Data.Map.Strict as Map

import LexLatte
import ParLatte
import PrintLatte
import AbsLatte
import Frontend
import Compiler

import ErrM

type ParseFun a = [Token] -> Err a

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> Bool -> ParseFun Program -> FilePath -> IO ()
runFile v link_libc p f = do
    putStrV v f
    readFile f >>= run v p >>= (writeFile outf)
    callCommand $ "gcc -c " ++ outf ++ " -o " ++ objf
    if link_libc then
        callCommand $ "gcc -no-pie -nostartfiles -lc -o " ++ exef ++ " lib/runtime.o " ++ objf
    else
        callCommand $ "ld -o " ++ exef ++ " lib/runtime.o lib/malloc.o " ++ objf
    where
    outf = dropExtension f ++ ".s"
    objf = dropExtension f ++ ".o"
    exef = dropExtension f

run :: Verbosity -> ParseFun Program -> String -> IO String
run v p s = let ts = myLexer s in case p ts of
    Bad err -> do
        hPutStrLn stderr "ERROR"
        putStrLn "Parse Failed:"
        putStrV v "Tokens:"
        putStrV v $ show ts
        putStrLn $ err ++ "\n"
        exitFailure
    Ok program -> case runCheckProgram program of
        Right types -> do
            hPutStrLn stderr "OK"
            return $ compileProgram types program
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
    , "  --libc          Use libc malloc instead of provided one (creates dynamically linked binary instead of statically)"
    ]
  exitFailure

main :: IO ()
main = do
    args <- getArgs
    let link_libc = elem "--libc" args
    let nargs = args \\ ["--libc"]
    case nargs of
        ["--help"] -> usage
        [] -> getContents >>= run 0 pProgram >>= putStrLn >> exitSuccess
        "-v":fs -> mapM_ (runFile 2 link_libc pProgram) fs >> exitSuccess
        fs -> mapM_ (runFile 0 link_libc pProgram) fs >> exitSuccess
