module Interpreter where

import AbsLattePlus
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import System.IO

type PInfo = Maybe(Int, Int)

data Var = VVoid
    | VInt Integer
    | VBool Bool
    | VString String

data Func = VFunc ([Expr PInfo] -> Interpreter Var)

type Loc = Int
type VEnv = M.Map Ident Loc
type FEnv = M.Map Ident Func
type Env = (VEnv, FEnv)
type Store = M.Map Loc Var

type XResult = ExceptT String IO
type XReader = ReaderT Env XResult
type Interpreter = StateT Store XReader

atPosition :: PInfo -> String
atPosition (Just (line, column)) = show line ++ ":" ++ show column ++ ": "
atPosition Nothing = ": "

getPosition :: Expr PInfo -> PInfo
getPosition exp = case exp of
    EVar pi _ -> pi
    ELitInt pi _ -> pi
    ELitTrue pi -> pi
    ELitFalse pi -> pi
    EApp pi _ _ -> pi
    EString pi _ -> pi
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
        TString _ -> return (VString "")
        TVoid _ -> return VVoid

alloc :: Interpreter Loc
alloc = do
    store <- get
    return (if (M.null store) then 1 else (fst (M.findMax store) + 1))

semInt :: Expr PInfo -> Interpreter Integer
semInt expr = do
    store <- get
    (vEnv, fEnv) <- ask
    val <- semExpr expr
    case val of
        VInt x -> return x
        _ -> throwError (atPosition (getPosition expr) ++ "int expected")

semBool :: Expr PInfo -> Interpreter Bool
semBool expr = do
    store <- get
    (vEnv, fEnv) <- ask
    val <- semExpr expr
    case val of
        VBool x -> return x
        _ -> throwError (atPosition (getPosition expr) ++ "bool expected")

semExpr :: Expr PInfo -> Interpreter Var
semExpr expr = do
    store <- get
    (vEnv, fEnv) <- ask
    case expr of
        EVar pi vName -> case M.lookup vName vEnv of
            Nothing -> throwError (atPosition (getPosition expr) ++ "variable " ++ show vName ++ " not declared")
            Just loc -> case M.lookup loc store of
                Nothing -> throwError (atPosition (getPosition expr) ++ "no value at location: " ++ show loc)
                Just var -> return var
        ELitInt _ n -> return (VInt n)
        ELitTrue _ -> return (VBool True)
        ELitFalse _ -> return (VBool False)
        EApp pi fName exprs -> case M.lookup fName fEnv of
            Just (VFunc f) -> f exprs
            _ -> throwError (atPosition (getPosition expr) ++ "function " ++ show fName ++ " not declared")
        EString _ s -> return (VString s)
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
                    0 -> throwError (atPosition (getPosition exp2) ++ "division by 0")
                    _ -> return (VInt (val1 `mod` val2))
                ODiv _ -> case val2 of
                    0 -> throwError (atPosition (getPosition exp2) ++ "modulo by 0")
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

semVDecl :: VDecl PInfo -> Interpreter Env
semVDecl (DVar _ t i) = do
    (vEnv, fEnv) <- ask
    newLoc <- alloc
    newVal <- case i of
            NoInit _ _ -> defaultValue t
            Init _ _ expr -> semExpr expr
    let vName = case i of
            NoInit _ x -> x
            Init _ x _ -> x
    modify (M.insert newLoc newVal)
    return ((M.insert vName newLoc vEnv), fEnv)

semVDecls :: [VDecl PInfo] -> Interpreter Env
semVDecls [] = ask
semVDecls (d:ds) = do
    newEnv <- semVDecl d
    local (const newEnv) (semVDecls ds)

semFDef :: FDef PInfo -> Interpreter Env
semFDef (DFun pi t fName args (FBody _ decls stmts ret)) =
    do
        (vEnv, fEnv) <- ask
        return (vEnv, (M.insert fName (VFunc func) fEnv))
        where
            func :: [Expr PInfo] -> Interpreter Var
            func exprs =
                do
                    when (length exprs /= length args) (throwError ("function" ++ show fName ++ "called with wrong number of arguments")) -- TODO: position

                    (vEnv, fEnv) <- ask
                    argEnv <- local (const (vEnv, (M.insert fName (VFunc func) fEnv))) (setArgsFromExprs (zip args exprs))
                    declEnv <- local (const argEnv) (semVDecls decls)
                    semStmts stmts

                    local (const declEnv) (case ret of
                                            RetVoid _ -> return VVoid
                                            RetVal _ expr -> semExpr expr)

            setArgFromExpr :: (Arg PInfo, Expr PInfo) -> Interpreter Env
            setArgFromExpr (ArgVal _ t argName, expr) =
                do
                    (vEnv, fEnv) <- ask
                    newLoc <- alloc
                    newVal <- semExpr expr

                    modify (M.insert newLoc newVal)
                    return ((M.insert argName newLoc vEnv), fEnv)
            setArgFromExpr (ArgRef _ t argName, expr) =
                do
                    (vEnv, fEnv) <- ask

                    case expr of
                        EVar _ vName ->
                            case M.lookup vName vEnv of
                                Nothing
                                    -> throwError (atPosition (getPosition expr) ++ "variable " ++ show vName ++ " not declared")
                                Just loc
                                    -> return ((M.insert argName loc vEnv), fEnv)
                        _ -> throwError (atPosition (getPosition expr) ++ "Argument passed by reference is not a variable")

            setArgsFromExprs :: [(Arg PInfo, Expr PInfo)] -> Interpreter Env
            setArgsFromExprs [] = ask
            setArgsFromExprs (z:zs) = do
                                        newEnv <- setArgFromExpr z
                                        local (const newEnv) (setArgsFromExprs zs)

semFDefs :: [FDef PInfo] -> Interpreter Env
semFDefs [] = ask
semFDefs (d:ds) = do
    newEnv <- semFDef d
    local (const newEnv) (semFDefs ds)

semStmt :: Stmt PInfo -> Interpreter ()
semStmt stmt = do
    store <- get
    (vEnv, fEnv) <- ask
    case stmt of
        SEmpty _ -> return ()
        SBlock _ (Blk _ ds stmts) -> do
            vdelcEnv <- semVDecls ds
            local (const vdelcEnv) (semStmts stmts)
            return ()
        SAssign _ vName expr -> do
            val <- semExpr expr
            case M.lookup vName vEnv of
                Nothing -> throwError (atPosition (getPosition expr) ++ "variable " ++ show vName ++ " not declared")
                Just loc -> modify (M.insert loc val) >> return ()
        SCond _ expr stmt -> do
            cond <- semBool expr
            if cond then semStmt stmt else return ()
        SCondElse _ expr (Blk _ dsTrue stmtsTrue) (Blk _ dsFalse stmtsFalse) -> do
            cond <- semBool expr
            let (ds, stmts) = if cond then (dsTrue, stmtsTrue) else (dsFalse, stmtsFalse)
            vdeclEnv <- semVDecls ds
            local (const vdeclEnv) (semStmts stmts)
            return ()
        SWhile _ expr innerStmt -> do
            cond <- semBool expr
            if cond then semStmt innerStmt >> semStmt stmt else return ()
        SExp _ expr -> do
            _ <- semExpr expr
            return ()

semStmts :: [Stmt PInfo] -> Interpreter Env
semStmts [] = ask
semStmts (stmt:stmts) = do
    semStmt stmt
    semStmts stmts

startStore :: Store
startStore = M.empty

startEnv :: Env
startEnv = (M.empty, M.fromList [(Ident "print", VFunc printFunc)])
    where
        printFunc :: [Expr PInfo] -> Interpreter Var
        printFunc exprs = mapM_ (
            \expr -> semExpr expr >>= \val -> case val of
                VInt v -> lift $ lift $ lift $ hPutStrLn stdout (show v)
                VBool b -> lift $ lift $ lift $ hPutStrLn stdout (show b)
                VString s -> lift $ lift $ lift $ hPutStrLn stdout s
                _ -> throwError (atPosition (getPosition expr) ++ "print argument of invalid type")
            ) exprs >> return VVoid

startInterpreter :: Program PInfo -> Interpreter ()
startInterpreter (Prog _ vDecls fDefs) = do
    modify (const startStore)
    vdeclEnv <- local (const startEnv) (semVDecls vDecls)
    fdefEnv <- local (const vdeclEnv) (semFDefs fDefs)
    when (M.notMember (Ident "main") (snd fdefEnv)) (throwError "main() undeclared")
    local (const fdefEnv) (semExpr (EApp Nothing (Ident "main") []))
    return ()

interpret :: Program PInfo -> XResult ()
interpret program = do
    runReaderT (execStateT (startInterpreter program) M.empty) (M.empty, M.empty)
    return ()

runInterpreter :: Program PInfo -> IO ()
runInterpreter program = do
    interpretation <- runExceptT (interpret program)
    case interpretation of
        Left error -> hPutStrLn stderr ("Runtime error: " ++ error)
        Right io -> return io