module Interpreter where

import AbsLattePlus
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

type PInfo = Maybe(Int, Int)

data Var =
    VInt Int
    | VBool Bool
    | VVoid

instance Eq Var where
    (VInt x) == (VInt y) = x == y
    (VBool x) == (VBool y) = x == y
    VVoid == VVoid = True
    _ == _ = False

instance Show Var where
    show (VInt x) = show x
    show (VBool x) = show x
    show VVoid = "()"

type Loc = Int
type Env = M.Map Ident Loc
type Store = M.Map Loc Var

type XExcept = ExceptT String IO
type XState = StateT Store XExcept
type Interpreter = ReaderT Env XState

interpret :: Program (PInfo) -> IO ()
interpret program@(Prog pi vs fs) = undefined