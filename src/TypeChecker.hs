module TypeChecker where

import AbsLattePlus

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Map as M

import System.IO

import Utils ( atPosition, getPosition, PInfo )

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

toTCType :: Type PInfo -> TCType
toTCType t = case t of
    TInt _ -> TCInt
    TString _ -> TCString
    TBool _ -> TCBool
    TVoid _ -> TCVoid

alloc :: TC Loc
alloc = do
    store <- get
    return (if M.null store then 1 else fst (M.findMax store) + 1)

enforce :: TCType -> Expr PInfo -> TC TCType
enforce expected expr = do
    got <- checkExpr expr
    if expected == got then
        return got
    else
        throwError (atPosition (getPosition expr) ++ show expected ++ " expected, got " ++ show got)

checkExpr :: Expr PInfo -> TC TCType
checkExpr expr = do
    store <- get
    (vEnv, fEnv) <- ask
    case expr of
        EVar pi vName@(Ident vNameString) -> case M.lookup vName vEnv of
            Just loc -> case M.lookup loc store of
                Just t -> return t
                Nothing -> throwError (atPosition (getPosition expr)
                            ++ "TypeChecker internal error - reference to empty location")
            Nothing -> throwError (atPosition pi
                        ++ "variable " ++ vNameString ++ " not declared")
        ELitInt _ n -> return TCInt
        ELitTrue _ -> return TCBool
        ELitFalse _ -> return TCBool
        EApp pi fName@(Ident fNameString) exprs -> case M.lookup fName fEnv of
            Just (TCFunc args retType) -> do
                if length args /= length exprs then
                    throwError (atPosition pi ++ "function " ++ fNameString
                        ++ " called with wrong number of arguments")
                else
                    do
                        _ <- checkArgs (zip args exprs)
                        return retType
                            where
                                checkArg :: (TCArg, Expr PInfo) -> TC ()
                                checkArg (TCArgRef expectedType, EVar pi vName) = do
                                    store <- get
                                    (vEnv, fEnv) <- ask
                                    case M.lookup vName vEnv of
                                        Nothing -> throwError (atPosition pi
                                            ++ "argument passed by reference is not a variable")
                                        Just loc -> case M.lookup loc store of
                                            Just gotType -> if gotType == expectedType then
                                                                return ()
                                                            else
                                                                throwError (atPosition pi
                                                                    ++ "expected &" ++ show expectedType
                                                                    ++ ", got &" ++ show gotType)
                                            Nothing -> throwError (atPosition (getPosition expr)
                                                ++ "TypeChecker internal error - reference to empty location")
                                checkArg (TCArgRef _, expr) =
                                    throwError (atPosition (getPosition expr)
                                        ++ "non-variable passed by reference")
                                checkArg (TCArgVal expectedType, expr) = do
                                    gotType <- checkExpr expr
                                    if gotType == expectedType then
                                        return ()
                                    else
                                        throwError (atPosition (getPosition expr)
                                            ++ show expectedType ++ " expected, got " ++ show gotType)

                                checkArgs :: [(TCArg, Expr PInfo)] -> TC ()
                                checkArgs [] = return ()
                                checkArgs (z:zs) = checkArg z >> checkArgs zs
            Nothing -> throwError (atPosition pi ++ "function " ++ fNameString ++ " not declared")
        EString _ s -> return TCString
        ENeg _ exp -> enforce TCInt exp >> return TCInt
        ENot _ exp -> enforce TCBool exp >> return TCBool
        EMul _ exp1 op exp2 -> enforce TCInt exp1 >> enforce TCInt exp2 >> return TCInt
        EAdd _ exp1 op exp2 -> enforce TCInt exp1 >> enforce TCInt exp2 >> return TCInt
        ECmp _ exp1 cmp exp2 -> enforce TCInt exp1 >> enforce TCInt exp2 >> return TCBool
        EAnd _ exp1 exp2 -> enforce TCBool exp1 >> enforce TCBool exp2 >> return TCBool
        EOr _ exp1 exp2 -> enforce TCBool exp1 >> enforce TCBool exp2 >> return TCBool

checkVDecl :: VDecl PInfo -> TC Env
checkVDecl (DVar _ t i) = do
    (vEnv, fEnv) <- ask
    newLoc <- alloc
    newVal <- case i of
        NoInit _ _ -> return (toTCType t)
        Init pi _ expr -> do
            gotType <- checkExpr expr
            let expectedType = toTCType t
            if gotType == expectedType then
                return gotType
            else
                throwError (atPosition pi
                    ++ show expectedType ++ " expected, got " ++ show gotType)
    let vName = case i of
            NoInit _ x -> x
            Init _ x _ -> x
    modify (M.insert newLoc newVal)
    return (M.insert vName newLoc vEnv, fEnv)

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
        let expectedType = toTCType t
        let newEnv = (vEnv, M.insert fName (TCFunc tcArgs (toTCType t)) fEnv)
        gotType <- func newEnv
        if gotType == expectedType then
            return newEnv
        else
            throwError (atPosition pi ++ show expectedType ++ " return type expected, got " ++ show gotType)
        where
            func :: Env -> TC TCType
            func funcEnv =
                do
                    argEnv <- local (const funcEnv) (setEnvFromArgs args)
                    declEnv <- local (const argEnv) (checkVDecls decls)
                    local (const declEnv) (checkStmts stmts)
                    local (const declEnv) (case ret of
                        RetVoid _ -> return TCVoid
                        RetVal _ expr -> checkExpr expr)

            setEnvFromAnyArg :: Type PInfo -> Ident -> TC Env
            setEnvFromAnyArg t argName = do
                (vEnv, fEnv) <- ask
                newLoc <- alloc
                modify (M.insert newLoc (toTCType t))
                return (M.insert argName newLoc vEnv, fEnv)

            setEnvFromArg :: Arg PInfo -> TC Env
            setEnvFromArg (ArgVal _ t argName) = setEnvFromAnyArg t argName
            setEnvFromArg (ArgRef _ t argName) = setEnvFromAnyArg t argName

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
        SAssign pi vName@(Ident vNameString) expr -> do
            gotType <- checkExpr expr
            case M.lookup vName vEnv of
                Just loc -> case M.lookup loc store of
                    Just expectedType -> do
                        if expectedType == gotType then
                            return ()
                        else
                            throwError (atPosition pi
                                ++ show expectedType ++ " expected, got " ++ show gotType)
                    Nothing -> throwError (atPosition pi
                                ++ "TypeChecker internal error - reference to empty location")
                Nothing -> throwError (atPosition pi
                                ++ "variable " ++ vNameString ++ " not declared")
        SCond _ expr stmt -> enforce TCBool expr >> checkStmt stmt >> return ()
        SCondElse _ expr (Blk _ dsTrue stmtsTrue) (Blk _ dsFalse stmtsFalse) -> do
            _ <- enforce TCBool expr
            trueEnv <- checkVDecls dsTrue
            local (const trueEnv) (checkStmts stmtsTrue)
            falseEnv <- checkVDecls dsFalse
            local (const falseEnv) (checkStmts stmtsFalse)
            return ()
        SWhile _ expr innerStmt -> enforce TCBool expr >> checkStmt innerStmt >> return ()
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