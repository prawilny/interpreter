module TypeChecker where

import AbsLattePlus
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import System.IO

type PInfo = Maybe(Int, Int)

data TCType = TCVoid
    | TCInt
    | TCBool
    | TCString

instance Show TCType where
    show TCVoid = "void"
    show TCInt = "int"
    show TCBool = "bool"
    show TCString = "string"

instance Eq TCType where
    TCVoid == TCVoid = True
    TCInt == TCInt = True
    TCBool == TCBool = True
    TCString == TCString = True
    _ == _ = False

data TCArg = TCArgVal TCType | TCArgRef TCType

data TCFunc = TCFunc [TCArg] TCType

type Loc = Int
type VEnv = M.Map Ident Loc
type FEnv = M.Map Ident TCFunc
type Env = (VEnv, FEnv)
type Store = M.Map Loc TCType

type TCResult = ExceptT String IO
type TCReader = ReaderT Env TCResult
type TC = StateT Store TCReader

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

toTCType :: Type PInfo -> TCType
toTCType t = case t of
    TInt _ -> TCInt
    TString _ -> TCString
    TBool _ -> TCBool
    TVoid _ -> TCVoid

alloc :: TC Loc
alloc = do
    store <- get
    return (if (M.null store) then 1 else (fst (M.findMax store) + 1))

checkInt :: Expr PInfo -> TC TCType
checkInt expr = do
    store <- get
    env <- ask
    val <- checkExpr expr
    case val of
        TCInt -> return TCInt
        _ -> throwError (atPosition (getPosition expr) ++ "int expected")

checkBool :: Expr PInfo -> TC TCType
checkBool expr = do
    store <- get
    env <- ask
    val <- checkExpr expr
    case val of
        TCBool -> return TCBool
        _ -> throwError (atPosition (getPosition expr) ++ "bool expected")

checkExpr :: Expr PInfo -> TC TCType
checkExpr expr = do
    store <- get
    (vEnv, fEnv) <- ask
    case expr of
        EVar pi vName -> case M.lookup vName vEnv of
            Nothing -> throwError (atPosition (getPosition expr) ++ "variable " ++ show vName ++ " not declared")
            Just loc -> case M.lookup loc store of
                Nothing -> throwError (atPosition (getPosition expr) ++ "no value at location: " ++ show loc)
                Just t -> return t
        ELitInt _ n -> return TCInt
        ELitTrue _ -> return TCBool
        ELitFalse _ -> return TCBool
        EApp pi fName exprs -> case M.lookup fName fEnv of
            Just (TCFunc args tctype) -> do
                if (length args /= length exprs) then
                    throwError "function called with bad number of arguments"
                else
                    do
                        _ <- checkArgs (zip args exprs)
                        return tctype
                            where
                                checkArg :: (TCArg, Expr PInfo) -> TC ()
                                checkArg (TCArgRef expectedType, EVar _ vName) = do
                                    store <- get
                                    (vEnv, fEnv) <- ask
                                    case M.lookup vName vEnv of
                                        Nothing -> throwError "argument passed by reference is not a variable"
                                        Just loc -> case M.lookup loc store of
                                            Just gotType -> if (gotType == expectedType) then
                                                                return ()
                                                            else
                                                                throwError ("expected " ++ show expectedType)
                                            Nothing -> throwError "something should've been here..."
                                checkArg (TCArgRef _, _) = throwError "non-variable passed by reference"
                                checkArg (TCArgVal expectedType, expr) = do
                                    gotType <- checkExpr expr
                                    if (gotType == expectedType) then
                                        return ()
                                    else
                                        throwError ("expected " ++ show expectedType)

                                checkArgs :: [(TCArg, Expr PInfo)] -> TC ()
                                checkArgs [] = return ()
                                checkArgs (z:zs) = checkArg z >> checkArgs zs

            _ -> throwError (atPosition (getPosition expr) ++ "function " ++ show fName ++ " not declared")
        EString _ s -> return TCString
        ENeg _ exp -> checkInt exp >> return TCInt
        ENot _ exp -> checkBool exp >> return TCBool
        EMul _ exp1 op exp2 -> checkInt exp1 >> checkInt exp2 >> return TCInt
        EAdd _ exp1 op exp2 -> checkInt exp1 >> checkInt exp2 >> return TCInt
        ECmp _ exp1 cmp exp2 -> checkInt exp1 >> checkInt exp2 >> return TCInt
        EAnd _ exp1 exp2 -> checkInt exp1 >> checkInt exp2 >> return TCBool
        EOr _ exp1 exp2 -> checkInt exp1 >> checkInt exp2 >> return TCBool

checkVDecl :: VDecl PInfo -> TC Env
checkVDecl (DVar _ t i) = do
    (vEnv, fEnv) <- ask
    newLoc <- alloc
    newVal <- case i of
        NoInit pi _ -> return (toTCType t)
        Init pi _ expr -> do
            exprType <- checkExpr expr
            if (exprType == (toTCType t)) then
                return exprType
            else
                throwError ("excepted " ++ show (toTCType t))
    let vName = case i of
            NoInit _ x -> x
            Init _ x _ -> x
    modify (M.insert newLoc newVal)
    return ((M.insert vName newLoc vEnv), fEnv)

checkVDecls :: [VDecl PInfo] -> TC Env
checkVDecls [] = ask
checkVDecls (d:ds) = do
    newEnv <- checkVDecl d
    local (const newEnv) (checkVDecls ds)

checkFDef :: FDef PInfo -> TC Env
checkFDef (DFun pi t fName args (FBody _ decls stmts ret)) =
    do
        (vEnv, fEnv) <- ask
        let tcArgs = fmap (\arg -> case arg of
                                    ArgVal _ t _ -> TCArgVal (toTCType t)
                                    ArgRef _ t _ -> TCArgRef (toTCType t)
                                    ) args
        let newEnv = (vEnv, (M.insert fName (TCFunc tcArgs (toTCType t)) fEnv))
        _ <- func newEnv
        return newEnv
        where
            func :: Env -> TC TCType
            func funcEnv =
                do
                    argEnv <- local (const funcEnv) (setEnvFromArgs args)
                    declEnv <- local (const argEnv) (checkVDecls decls)
                    local (const declEnv) (checkStmts stmts)
                    local (const declEnv) (case ret of
                                            RetVoid _ -> case toTCType t of
                                                TCVoid -> return TCVoid
                                                _ -> throwError "nonvoid function returns void"
                                            RetVal _ expr -> do
                                                    resultType <- checkExpr expr
                                                    if (resultType == toTCType t) then
                                                        return resultType
                                                    else
                                                        throwError ("excepted " ++ show (toTCType t))
                                                )

            setEnvFromArg :: Arg PInfo -> TC Env
            setEnvFromArg (ArgVal _ t argName) = do
                (vEnv, fEnv) <- ask
                newLoc <- alloc
                modify (M.insert newLoc (toTCType t))
                return ((M.insert argName newLoc vEnv), fEnv)
            setEnvFromArg (ArgRef _ _ argName) = setEnvFromArg (ArgVal Nothing t argName)

            setEnvFromArgs :: [Arg PInfo] -> TC Env
            setEnvFromArgs [] = ask
            setEnvFromArgs (z:zs) = do
                newEnv <- setEnvFromArg z
                local (const newEnv) (setEnvFromArgs zs)

checkFDefs :: [FDef PInfo] -> TC Env
checkFDefs [] = ask
checkFDefs (d:ds) = do
    newEnv <- checkFDef d
    local (const newEnv) (checkFDefs ds)

checkStmt :: Stmt PInfo -> TC ()
checkStmt stmt = do
    store <- get
    (vEnv, fEnv) <- ask
    case stmt of
        SEmpty _ -> return ()
        SBlock _ (Blk _ ds stmts) -> do
            vdeclEnv <- checkVDecls ds
            local (const vdeclEnv) (checkStmts stmts)
            return ()
        SAssign _ vName expr -> do
            val <- checkExpr expr
            case M.lookup vName vEnv of
                Nothing -> throwError (atPosition (getPosition expr) ++ "variable " ++ show vName ++ " not declared")
                Just loc -> case M.lookup loc store of
                    Just tctype -> do
                                    if tctype == val then
                                        return ()
                                    else
                                        throwError ("expected " ++ show tctype)
                    Nothing -> throwError "nothing in memory"
        SCond _ expr stmt -> checkBool expr >> checkStmt stmt >> return ()
        SCondElse _ expr (Blk _ dsTrue stmtsTrue) (Blk _ dsFalse stmtsFalse) -> do
            _ <- checkBool expr
            trueEnv <- checkVDecls dsTrue
            local (const trueEnv) (checkStmts stmtsTrue)
            falseEnv <- checkVDecls dsFalse
            local (const falseEnv) (checkStmts stmtsFalse)
            return ()
        SWhile _ expr innerStmt -> checkBool expr >> checkStmt innerStmt >> return ()
        SExp _ expr -> checkExpr expr >> return ()

checkStmts :: [Stmt PInfo] -> TC ()
checkStmts [] = return ()
checkStmts (stmt:stmts) = do
    checkStmt stmt
    checkStmts stmts

startStore :: Store
startStore = M.empty

startEnv :: Env
startEnv = (M.empty, M.fromList [(Ident "printString", TCFunc [TCArgVal TCString] TCVoid),
                                    (Ident "printInt", TCFunc [TCArgVal TCInt] TCVoid),
                                    (Ident "printBool", TCFunc [TCArgVal TCBool] TCVoid),
                                    (Ident "assert", TCFunc [TCArgVal TCBool, TCArgVal TCString] TCVoid),
                                    (Ident "concat", TCFunc [TCArgVal TCString, TCArgVal TCString] TCString)])

startTC :: Program PInfo -> TC ()
startTC (Prog _ vDecls fDefs) = do
    modify (const startStore)
    vdeclEnv <- local (const startEnv) (checkVDecls vDecls)
    fdefEnv <- local (const vdeclEnv) (checkFDefs fDefs)
    when (M.notMember (Ident "main") (snd fdefEnv)) (throwError "main() undeclared")
    local (const fdefEnv) (checkExpr (EApp Nothing (Ident "main") []))
    return ()

checkTypes :: Program PInfo -> TCResult ()
checkTypes program = do
    runReaderT (execStateT (startTC program) M.empty) (M.empty, M.empty)
    return ()

runTC :: Program PInfo -> IO ()
runTC program = do
    check <- runExceptT (checkTypes program)
    case check of
        Left error -> hPutStrLn stderr ("Runtime error: " ++ error)
        Right io -> return io