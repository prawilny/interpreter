module Interpreter where

import AbsLattePlus
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

type PInfo = Maybe(Int, Int)

data Var = VVoid
    | VInt Integer
    | VBool Bool

data Func = VFunc ([Expr PInfo] -> Interpreter Var)

type Loc = Int
type VEnv = M.Map Ident Loc
type FEnv = M.Map Ident Func
type Env = (VEnv, FEnv)
type Store = M.Map Loc Var

type XExcept = ExceptT String IO
type XReader = ReaderT Env XExcept
type Interpreter = StateT Store XReader

atPosition :: PInfo -> String
atPosition (Just (x, y)) = " at line " ++ show x ++ " position " ++ show y
atPosition Nothing = undefined

getPositionInfo :: Expr PInfo -> PInfo
getPositionInfo exp = case exp of
    EVar pi _ -> pi
    ELitInt pi _ -> pi
    ELitTrue pi -> pi
    ELitFalse pi -> pi
    EApp pi _ _ -> pi
    ENeg pi _ -> pi
    ENot pi _ -> pi
    EMul pi _ _ _ -> pi
    EAdd pi _ _ _ -> pi
    ECmp pi _ _ _ -> pi
    EAnd pi _ _ -> pi
    EOr pi _ _ -> pi

defaultValue :: Type PInfo -> Interpreter Var
defaultValue t = do
    case t of
        TInt _ -> return (VInt 0)
        TBool _ -> return (VBool False)

alloc :: Interpreter Loc
alloc = do
    store <- get
    return (if (M.null store) then 1 else fst (M.findMax store))

semInt :: Expr PInfo -> Interpreter Integer
semInt expr = do
    store <- get
    (vEnv, fEnv) <- ask
    val <- semExpr expr
    case val of
        VInt x -> return x
        _ -> throwError ("int expected" ++ atPosition (getPositionInfo expr))

semBool :: Expr PInfo -> Interpreter Bool
semBool expr = do
    store <- get
    (vEnv, fEnv) <- ask
    val <- semExpr expr
    case val of
        VBool x -> return x
        _ -> throwError ("bool expected" ++ atPosition (getPositionInfo expr))

semExpr :: Expr PInfo -> Interpreter Var
semExpr expr = do
    store <- get
    (vEnv, fEnv) <- ask
    case expr of
        EVar pi vName -> case M.lookup vName vEnv of
            Nothing -> throwError ("variable " ++ show vName ++ " not declared" ++ atPosition (getPositionInfo expr))
            Just loc -> case M.lookup loc store of
                Nothing -> throwError ("no value @ " ++ show loc ++ atPosition (getPositionInfo expr))
                Just var -> return var
        ELitInt _ n -> return (VInt n)
        ELitTrue _ -> return (VBool True)
        ELitFalse _ -> return (VBool False)
        EApp pi fName exprs
            -> case M.lookup fName fEnv of
                Just (VFunc f) -> f exprs
                _ -> throwError ("function " ++ show fName ++ " not declared" ++ atPosition (getPositionInfo expr))
        ENeg _ exp -> do
            val <- semInt exp
            return (VInt (-1 * val))
        ENot _ exp -> do
            val <- semBool exp
            return (VBool (not val))
        EMul _ exp1 op exp2 -> do
            val1 <- semInt exp1
            val2 <- semInt exp2
            case op of
                OTimes _ -> return (VInt (val1 * val2))
                OMod _ -> case val2 of
                    0 -> throwError (show exp2 ++ " evaluates to 0" ++ atPosition (getPositionInfo expr))
                    _ -> return (VInt (val1 `mod` val2))
                ODiv _ -> case val2 of
                    0 -> throwError (show exp2 ++ " evaluates to 0" ++ atPosition (getPositionInfo expr))
                    _ -> return (VInt (val1 `div` val2))
        EAdd _ exp1 op exp2 -> do
            val1 <- semInt exp1
            val2 <- semInt exp2
            case op of
                OPlus _ -> return (VInt (val1 + val2))
                OMinus _ -> return (VInt (val1 - val2))
        ECmp _ exp1 cmp exp2 -> do
            val1 <- semInt exp1
            val2 <- semInt exp2
            case cmp of
                CLTH _ -> return (VBool (val1 < val2))
                CLEQ _ -> return (VBool (val1 <= val2))
                CGTH _ -> return (VBool (val1 > val2))
                CGEQ _ -> return (VBool (val1 >= val2))
                CEQU _ -> return (VBool (val1 == val2))
                CNEQ _ -> return (VBool (val1 /= val2))
        EAnd _ exp1 exp2 -> do
            val1 <- semBool exp1
            val2 <- semBool exp2
            return (VBool (val1 && val2))
        EOr _ exp1 exp2 -> do
            val1 <- semBool exp1
            val2 <- semBool exp2
            return (VBool (val1 || val2))

semVDecl :: VDecl PInfo -> Interpreter () -> Interpreter ()
semVDecl (DVar _ t i) interpreter = do
    newLoc <- alloc
    newVal <- case i of
                    NoInit _ _ -> defaultValue t
                    Init _ _ expr -> semExpr expr
    let vName = case i of
                    NoInit _ x -> x
                    Init _ x _ -> x
    modify (M.insert newLoc newVal)
    local (\(vEnv, fEnv) -> ((M.insert vName newLoc vEnv), fEnv)) interpreter

semVDecls :: [VDecl PInfo] -> Interpreter () -> Interpreter ()
semVDecls ds interpreter = foldl (flip semVDecl) interpreter ds

semFDef :: FDef PInfo -> Interpreter () -> Interpreter ()
semFDef (DFun pi t fName args (FBody _ decls stmts ret)) interpreter =
    do
        (vEnv, fEnv) <- ask
        let newEnv = (vEnv, fEnv)
        local (\(vEnv, fEnv) -> (vEnv, (M.insert fName (VFunc f) fEnv))) interpreter
        where
            f :: [Expr PInfo] -> Interpreter Var
            f exprs =
                do
                    when (length exprs /= length args) (throwError ("function" ++ show fName ++ "called with wrong number of arguments")) -- TODO: position
                    postStmtsInterpreter <- semStmts stmts (semVDecls decls (setArgsFromExprs (zip args exprs) interpreter))
                    case ret of
                        RetVoid _ -> return VVoid
                        RetVal _ expr -> do
                                            retval <- semExpr expr
                                            return retval

            setArgFromExpr :: (Arg PInfo, Expr PInfo) -> Interpreter () -> Interpreter ()
            setArgFromExpr (ArgVal _ t argName, expr) inter = do
                newLoc <- alloc
                newVal <- semExpr expr

                modify (M.insert newLoc newVal)

                let goodType = case (t, newVal) of
                                (TInt _, VInt _) -> True
                                (TBool _, VBool _) -> True
                                _ ->  False

                if not goodType
                    then
                        throwError ("wrong argument type" ++ atPosition (getPositionInfo expr))
                    else
                        local (\(vEnv, fEnv) -> ((M.insert argName newLoc vEnv), fEnv)) inter

            setArgsFromExprs :: [(Arg PInfo, Expr PInfo)] -> Interpreter () -> Interpreter ()
            setArgsFromExprs zipArgsExprs inter = foldl (flip setArgFromExpr) inter zipArgsExprs

semFDefs :: [FDef PInfo] -> Interpreter () -> Interpreter ()
semFDefs ds interpreter = foldl (flip semFDef) interpreter ds

semStmt :: Stmt PInfo -> Interpreter () -> Interpreter ()
semStmt stmt interpreter = do
    store <- get
    (vEnv, fEnv) <- ask
    case stmt of
        SEmpty _
            -> interpreter
        SBlock _ (Blk _ ds stmts)
            -> semStmts stmts (semVDecls ds interpreter)
        SAssign _ vName expr
            -> do
                val <- semExpr expr
                case M.lookup vName vEnv of
                    Nothing -> throwError ("variable " ++ show vName ++ " not declared" ++ atPosition (getPositionInfo expr))
                    Just loc
                        -> local (\(vEnv, fEnv) -> ((M.insert vName loc vEnv), fEnv)) interpreter

        SCond _ expr stmt
            -> do
                cond <- semBool expr
                if cond then semStmt stmt interpreter else interpreter
        SCondElse _ expr (Blk _ dsTrue stmtsTrue) (Blk _ dsFalse stmtsFalse)
            -> do
                cond <- semBool expr
                let (ds, stmts) = if cond then (dsTrue, stmtsTrue) else (dsFalse, stmtsFalse)
                semStmts stmts (semVDecls ds interpreter)
        SWhile _ expr stmt
            -> do
                cond <- semBool expr
                if cond then semStmt stmt interpreter else interpreter
        SExp _ expr
            -> do
                _ <- semExpr expr
                interpreter

semStmts :: [Stmt PInfo] -> Interpreter () -> Interpreter ()
semStmts [] interpreter = interpreter
semStmts stmts interpreter = foldl (flip semStmt) interpreter stmts

interpret :: Program PInfo -> IO ()
interpret program@(Prog _ vs fs) =
    do
        return ()