module Main where

import System.IO
import System.Environment
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)
import System.FilePath
import System.Directory
import System.Process
import Control.Monad.State
import Data.List

import LexLatte
import ParLatte
--import PrintLatte
import AbsLatte
import Frontend
import ErrM
import Frontend
import Compiler

type ParseFun a = [Token] -> Err a

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO Bool
runFile v p f = do
    prog <- putStrV v f >> readFile f >>= run v p
    if prog == "" then return False else do
        writeFile outf prog
        callCommand $ "gcc -c " ++ outf ++ " -o " ++ objf
        callCommand $ "gcc -no-pie -nostartfiles -lc -o " ++ exef ++ " lib/runtime.o " ++ objf
        callCommand $ "./" ++ exef ++ " > " ++ resf
        res <- readFile resf
        corout <- readFile $ dropExtension f ++ ".output"
        return (res == corout)
    where
    outf = dropExtension f ++ ".s"
    objf = dropExtension f ++ ".o"
    exef = dropExtension f
    resf = dropExtension f ++ ".res"


run :: Verbosity -> ParseFun Program -> String -> IO String
run _ p s = let ts = myLexer s in case p ts of
    Bad err -> do
        hPutStrLn stderr "ERROR"
        putStrLn "Parse Failed:"
        putStrLn $ err ++ "\n"
        return ""
    Ok program -> case runCheckProgram program of
        Right types -> do
            hPutStrLn stderr "OK"
            return $ compileProgram types program
        Left exc -> hPutStrLn stderr "ERROR" >> putStrLn "Semantic check failed:" >> putStrLn (show exc) >> return ""

allFilesIn :: FilePath -> IO [FilePath]
allFilesIn dir = (map (dir++)) <$>
    filter (isSuffixOf ".lat") <$>
    filter (/= "..") <$>
    filter(/= ".") <$>
    getDirectoryContents dir

foldTests :: Bool -> Bool -> [Bool] -> FilePath -> IO [Bool]
foldTests do_exit_fail good_res res path = do
    r <- runFile 2 pProgram path
    if do_exit_fail && r /= good_res then exitFailure
    else return (r:res)

main :: IO ()
main = do
    args <- getArgs
    let do_test_good = not (elem "bad" args) || elem "good" args
    let do_test_bad = not (elem "good" args) || elem "bad" args
    let do_exit_fail = elem "fail" args
    tests_good <- (\\ ["test/lattests/good/core018.lat"]) <$> allFilesIn "test/lattests/good/"
    tests_bad <- allFilesIn "test/lattests/bad/"
    res_good <-
        if do_test_good then liftM reverse $
            foldM (foldTests do_exit_fail True) [] tests_good
        else return []
    res_bad <-
        if do_test_bad then liftM reverse $
            foldM (foldTests do_exit_fail False) [] tests_bad
        else return []
    let rg = foldl (&&) True res_good
    let rb = not $ foldl (||) False res_bad
    if rg then putStrLn "Good tests Succeeded"
    else putStrLn "Failed good tests: " >>
        zipWithM_ (\r f -> if r then return () else putStrLn f) res_good tests_good
    if rb then putStrLn "Bad tests Succeeded"
    else putStrLn "Failed bad tests: " >>
        zipWithM_ (\r f -> if not r then return () else putStrLn f) res_bad tests_bad
    if rg && rb then exitSuccess else exitFailure

