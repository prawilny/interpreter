module Main where

import System.Environment ( getArgs )
import System.Exit ( exitFailure, exitSuccess )

import LexLattePlus
import ParLattePlus
import AbsLattePlus

import ErrM

import Interpreter ( runInterpreter )
import Utils ( PInfo )

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

runFile :: ParseFun (Program PInfo) -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: ParseFun (Program PInfo) -> String -> IO ()
run p s = let ts = myLLexer s in case p ts of
            Bad s   -> do
                        putStrLn "Interpreter failed to parse the program"
                        exitFailure
            Ok tree -> do
                        runInterpreter tree
                        exitSuccess

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Run interpreter on program from stdin"
    , "  filepath        Run interpreter on program from filepath"
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run pProgram
    [f] -> runFile pProgram f
    _ -> putStrLn "Too many arguments" >> exitFailure
