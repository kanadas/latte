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

runFile :: Verbosity -> Bool -> ParseFun Program -> FilePath -> IO Bool
runFile v link_libc p f = do
    prog <- putStrV v f >> readFile f >>= run v p
    if prog == "" then return False else do
        writeFile outf prog
        callCommand $ "gcc -c " ++ outf ++ " -o " ++ objf
        if link_libc then
            callCommand $ "gcc -no-pie -nostartfiles -lc -o " ++ exef ++ " lib/runtime.o " ++ objf
        else
            callCommand $ "ld -o " ++ exef ++ " lib/runtime.o lib/malloc.o " ++ objf
        is_input <- doesFileExist inf
        if is_input then
            callCommand $ "./" ++ exef ++ " < " ++ inf ++ " > " ++ resf
        else
            callCommand $ "./" ++ exef ++ " > " ++ resf
        res <- readFile resf
        corout <- readFile $ dropExtension f ++ ".output"
        return (res == corout)
    where
    outf = dropExtension f ++ ".s"
    objf = dropExtension f ++ ".o"
    exef = dropExtension f
    resf = dropExtension f ++ ".res"
    inf = dropExtension f ++ ".input"


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

foldTests :: Bool -> Bool -> Bool -> [Bool] -> FilePath -> IO [Bool]
foldTests link_libc do_exit_fail good_res res path = do
    r <- runFile 2 link_libc pProgram path
    if do_exit_fail && r /= good_res then exitFailure
    else return (r:res)

main :: IO ()
main = do
    args <- getArgs
    let link_libc = elem "--libc" args
    let nargs = args \\ ["--libc"]
    let do_test_good = nargs == [] || elem "good" nargs
    let do_test_bad = nargs == [] || elem "bad" nargs
    let do_test_runtime = elem "runtime" nargs
    let do_exit_fail = elem "fail" nargs
    tests_good <- allFilesIn "test/lattests/good/"
    tests_bad <- allFilesIn "test/lattests/bad/"
    tests_basic <- allFilesIn "test/mrjp-tests/good/basic/"
    --tests_gr5 <- allFilesIn "test/mrjp-tests/gr5/" --classes tests
    tests_bad2 <- allFilesIn "test/mrjp-tests/bad/semantic/"
    tests_runtime <- allFilesIn "test/mrjp-tests/bad/runtime/"
    res <- if do_test_good then do
        res_good <- liftM reverse $ foldM (foldTests link_libc do_exit_fail True) [] tests_good
        let rg = foldl (&&) True res_good
        if rg then putStrLn "Good tests Succeeded"
        else putStrLn "Failed good tests: " >>
            zipWithM_ (\r f -> if r then return () else putStrLn f) res_good tests_good

        res_basic <- liftM reverse $ foldM (foldTests link_libc do_exit_fail True) [] tests_basic
        let rb = foldl (&&) True res_basic
        if rb then putStrLn "Basic tests Succeeded"
        else putStrLn "Failed basic tests: " >>
            zipWithM_ (\r f -> if r then return () else putStrLn f) res_basic tests_basic

        return $ rb && rg
    else return True
    res2 <- if do_test_bad then do
        res_bad <- liftM reverse $ foldM (foldTests link_libc do_exit_fail False) [] tests_bad
        let rb = not $ foldl (||) False res_bad
        if rb then putStrLn "Bad tests Succeeded"
        else putStrLn "Failed bad tests: " >>
            zipWithM_ (\r f -> if not r then return () else putStrLn f) res_bad tests_bad

        res_bad2 <- liftM reverse $ foldM (foldTests link_libc do_exit_fail False) [] tests_bad2
        let rb2 = not $ foldl (||) False res_bad2
        if rb2 then putStrLn "Bad tests Succeeded"
        else putStrLn "Failed bad tests: " >>
            zipWithM_ (\r f -> if not r then return () else putStrLn f) res_bad2 tests_bad2

        return $ rb && rb2
    else return True

    res3 <- if do_test_runtime then do
        res_runtime <- liftM reverse $ foldM (foldTests link_libc do_exit_fail False) [] tests_runtime
        let rr = not $ foldl (||) False res_runtime
        if rr then putStrLn "Bad tests Succeeded"
        else putStrLn "Failed bad tests: " >>
            zipWithM_ (\r f -> if not r then return () else putStrLn f) res_runtime tests_runtime

        return rr
    else return True

    if res && res2 && res3 then exitSuccess else exitFailure
