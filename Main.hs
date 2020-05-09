module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)

import LexLattePlus
import ParLattePlus
import SkelLattePlus
import PrintLattePlus
import AbsLattePlus

import ErrM

import Interpreter (runInterpreter)

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

runFile :: ParseFun (Program (Maybe (Int, Int))) -> FilePath -> IO ()
runFile p f = putStrLn f >> readFile f >>= run p

run :: ParseFun (Program (Maybe (Int, Int))) -> String -> IO ()
run p s = let ts = myLLexer s in case p ts of
            Bad s   -> do
                        exitFailure
            Ok tree -> do
                        runInterpreter tree
                        exitSuccess

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run pProgram
    fs -> mapM_ (runFile pProgram) fs
