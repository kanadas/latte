{-# LANGUAGE FlexibleContexts #-}
module Frontend (
    Exception,
    Trace,
    TEnv,
    initialTEnv,
    initialREnv,
    initialState,
    checkProgram,
    runCheckProgram
)where

import Control.Monad.Except
import Control.Monad.Trans.Reader
import Control.Monad.State.Lazy
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsLatte
import PrintLatte

data Exception =
      ERepeatedFun TopDef
    | ERepeatedArgName Ident TopDef
    | ENotReturning TopDef
    | EUnknownVar Ident Trace
    | EUnknownFun Ident Trace
    | EArgMismatch Type Type Trace
    | EWrongArgCnt Trace
    | ENotAFun Ident Type Trace
    | ETypeMismatch Expr Type Type Trace
    | EDoubleDecl Ident Trace
    | EVoidVar Item Trace
    | ETooBigConstant Integer Trace
    | EVoidArg TopDef
    | EWrongMain TopDef
    | EVoidReturn Expr Trace
    | ENoMain
    | ENotImplemented

instance Show Exception where
    show exc = case exc of
        ERepeatedFun topdef -> "Function with existing name: " ++ (printFunHead topdef)
        ERepeatedArgName ident topdef -> "Repeated argument name: " ++ show ident ++ " in function: " ++ printFunHead topdef
        ENotReturning topdef -> "Function without return: " ++ printFunHead topdef
        EUnknownVar ident trac -> "Unknown variable: " ++ show ident ++ " in: \n" ++ show trac
        EUnknownFun ident trac -> "Unknown function: " ++ show ident ++ " in: \n" ++ show trac
        EArgMismatch t1 t2 trac -> "Not matching argument types, expected " ++ show t2 ++
            " got " ++ show t1 ++ " in: \n" ++ show trac
        EWrongArgCnt trac -> "Wrong argument count in: \n" ++ show trac
        ENotAFun ident _ trac -> "Not a function: " ++ show ident ++ " in: \n" ++ show trac
        ETypeMismatch expr t1 t2 trac -> "Mismatching types in " ++ printTree expr ++
            "\nExpected " ++ show t2 ++ ", got " ++ show t1 ++ " in: \n" ++ show trac
        EDoubleDecl ident trac -> "Double declaration of symbol " ++ show ident ++
            " in \n" ++ show trac
        EVoidVar (NoInit ident) trac -> "Variable with void type: " ++ show ident ++ " in \n" ++ show trac
        EVoidVar (Init ident _) trac -> "Variable with void type: " ++ show ident ++ " in \n" ++ show trac
        ETooBigConstant n trac -> "Too big constant: " ++ show n ++ " in \n" ++ show trac
        EVoidArg topdef -> "Function with void argument: " ++ (printFunHead topdef)
        EWrongMain topdef -> "Wrond main definition: " ++ (printFunHead topdef)
        EVoidReturn expr trac -> "Returning value in void function: " ++ printTree expr ++ " in \n" ++ show trac
        ENoMain -> "No main function"
        ENotImplemented -> "Not implemented functionality"

printFunHead :: TopDef -> String
printFunHead (FnDef t ident arg _) = take (length s - 6) s ++ "\n"
    where s = printTree (FnDef t ident arg (Block []))

data Trace = Trace { tracFun :: TopDef, tracStmts :: [Stmt], tracExpr :: Maybe Expr }

instance Show Trace where
    show (Trace (FnDef _ ident _ _) stmts expr) = "  Function " ++ show ident ++
            traceExpr expr ++ traceStmts stmts
        where
        traceExpr (Just e) = "\n  Expression:\n" ++ printTree e
        traceExpr Nothing = ""
        traceStmts [stmt] = "\n  Statement:\n" ++ printTree stmt
        traceStmts (stmt:stmt2:_) = "\n  Statements:\n" ++ printTree stmt2 ++ printTree stmt
        traceStmts [] = ""

type TEnv = Map.Map Ident Type
data REnv = REnv { tenv :: TEnv, trace :: Trace }
type SEnv = TEnv
type Result a = ReaderT REnv (StateT SEnv (Either Exception)) a

appendTraceStmt :: Stmt -> REnv -> REnv
appendTraceStmt stmt (REnv x tr) = REnv x tr{tracStmts = stmt : (tracStmts tr)}

setTraceExpr :: Expr -> REnv -> REnv
setTraceExpr expr (REnv x tr) = REnv x tr{tracExpr = Just expr}

insideStmtTrace :: Stmt -> Trace -> Trace
insideStmtTrace stmt trac = trac{tracExpr = Nothing, tracStmts = (stmt:tracStmts trac)}

getCombEnv :: Result TEnv
getCombEnv = do
    lenv <- get
    asks $ (Map.union lenv).tenv

argsMap :: [Arg] -> TEnv
argsMap args = foldr (\(Arg t ident) acc -> Map.insert ident t acc) Map.empty args

checkProgram :: Program -> Result ()
checkProgram (Program topdefs) = mapM_ checkTopDef topdefs

checkTopDef :: TopDef -> Result ()
checkTopDef x = case x of
    FnDef t (Ident fname) args block -> do
        trac <- asks trace
        if (filter (\(Arg t _) -> t == Void) args) /= [] then
            throwError $ EVoidArg x
        else return ()
        if fname == "main" && (args /= [] || t /= Int) then
            throwError $ EWrongMain x
        else return ()
        put (argsMap args)
        rb <- local (\e -> e{trace = trac{tracFun = x}}) (checkBlock block)
        if rb || t == Void then return ()
        else throwError $ ENotReturning x

checkBlock :: Block -> Result Bool
checkBlock x = case x of
    Block stmts -> foldM (\acc stmt -> liftM (acc ||) (checkStmt stmt)) False stmts

--Returning if statement always returns
checkStmt :: Stmt -> Result Bool
checkStmt x = case x of
    Empty -> return False
    BStmt block -> do
        env <- getCombEnv
        stat <- get
        put Map.empty
        res <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkBlock block)
        put stat
        return res
    Decl t items -> if t == Void then do
                trac <- asks trace
                throwError $ EVoidVar (head items) (insideStmtTrace x trac)
            else mapM_ (checkItem x t) items >> return False
    Ass ident expr -> do
        te <- localCheckExpr x expr
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just t -> if t == te then return False
                else throwError $ ETypeMismatch expr te t (insideStmtTrace x trac)
            Nothing -> throwError $ EUnknownVar ident (insideStmtTrace x trac)
    Incr ident -> do
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just Int -> return False
            Just t -> throwError $ ETypeMismatch (EVar ident) t Int (insideStmtTrace x trac)
            Nothing -> throwError $ EUnknownVar ident (insideStmtTrace x trac)
    Decr ident -> do
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just Int -> return False
            Just t -> throwError $ ETypeMismatch (EVar ident) t Int trac
            Nothing -> throwError $ EUnknownVar ident (insideStmtTrace x trac)
    Ret expr -> do
        te <- localCheckExpr x expr
        trac <- asks trace
        case tracFun trac of
            FnDef t _ _ _ | t == Void -> throwError $ EVoidReturn expr (insideStmtTrace x trac)
            FnDef t _ _ _ | t == te -> return True
            FnDef t _ _ _ -> throwError $ ETypeMismatch expr te t (insideStmtTrace x trac)
    VRet -> do
        trac <- asks trace
        case tracFun trac of
            FnDef t ident _ _ -> if t == Void then return True
                else throwError $ ETypeMismatch (EVar ident) Void t (insideStmtTrace x trac)
    Cond expr stmt -> do
        te <- localCheckExpr x expr
        trac <- asks trace
        if te == Bool then do
            env <- getCombEnv
            stat <- get
            put Map.empty
            rets <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkStmt stmt)
            put stat
            if expr == ELitTrue && rets then return True else return False
        else throwError $ ETypeMismatch expr te Bool (insideStmtTrace x trac)
    CondElse expr stmt1 stmt2 -> do
        te <- localCheckExpr x expr
        trac <- asks trace
        if te == Bool then do
            env <- getCombEnv
            stat <- get
            put Map.empty
            ret1 <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkStmt stmt1)
            put Map.empty
            ret2 <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkStmt stmt2)
            put stat
            if expr == ELitTrue && ret1 then return True
            else if expr == ELitFalse && ret2 then return True
            else if ret1 && ret2 then return True
            else return False
        else throwError $ ETypeMismatch expr te Bool (insideStmtTrace x trac)
    While expr stmt -> do
        te <- localCheckExpr x expr
        trac <- asks trace
        if te == Bool then do
            env <- getCombEnv
            stat <- get
            put Map.empty
            rets <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkStmt stmt)
            put stat
            if expr == ELitTrue || rets then return True
            else return False
        else throwError $ ETypeMismatch expr te Bool (insideStmtTrace x trac)
    SExp expr -> local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr) >> return False

checkItem :: Stmt -> Type -> Item -> Result ()
checkItem stmt t x = case x of
    NoInit ident -> do
        env <- get
        trac <- asks trace
        if Map.member ident env then throwError $ EDoubleDecl ident (insideStmtTrace stmt trac)
        else modify (Map.insert ident t)
    Init ident expr -> do
        trac <- asks trace
        te <- localCheckExpr stmt expr
        if te == t then do
            env <- get
            if Map.member ident env then throwError $ EDoubleDecl ident (insideStmtTrace stmt trac)
            else modify (Map.insert ident t)
        else throwError $ ETypeMismatch expr te t (insideStmtTrace stmt trac)

localCheckExpr :: Stmt -> Expr -> Result Type
localCheckExpr s x = local ((appendTraceStmt s).(setTraceExpr x)) (checkExpr x)

checkExpr :: Expr -> Result Type
checkExpr x = case x of
    EVar ident -> do
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just t -> return t
            Nothing -> throwError $ EUnknownVar ident trac
    ELitInt n -> if abs n >= 2^(63 :: Integer) then do
            trac <- asks trace
            throwError $ ETooBigConstant n trac
        else return Int
    ELitTrue -> return Bool
    ELitFalse -> return Bool
    EApp ident exprs -> do
        args <- liftM reverse $ foldM (\acc expr -> liftM (:acc) (checkExpr expr)) [] exprs
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just (Fun t ts) -> checkArgList args ts where
                checkArgList (a:as) (b:bs) =
                    if a == b then checkArgList as bs
                    else throwError $ EArgMismatch a b trac
                checkArgList [] [] = return t
                checkArgList _ _ = throwError $ EWrongArgCnt trac
            Just t -> throwError $ ENotAFun ident t trac
            Nothing -> throwError $ EUnknownFun ident trac
    EString _ -> return Str
    Neg expr -> do
        t <- checkExpr expr
        trac <- asks trace
        if t == Int then return Int else throwError $ ETypeMismatch expr t Int trac
    Not expr -> do
        t <- checkExpr expr
        trac <- asks trace
        if t == Bool then return Bool
        else throwError $ ETypeMismatch expr t Bool trac
    EMul expr1 _ expr2 -> checkOp expr1 expr2 Int >> return Int
    EAdd expr1 Plus expr2 -> do
        t1 <- checkExpr expr1
        t2 <- checkExpr expr2
        trac <- asks trace
        if (t1 == t2 && (t1 == Int || t1 == Str)) then return t1
        else throwError $ ETypeMismatch x
            (if t1 == Int || t1 == Str then t2 else t1)
            (if t1 == Int || t1 == Str then t1 else if t2 == Int || t2 == Str then t2 else Int)
            trac
    EAdd expr1 _ expr2 -> checkOp expr1 expr2 Int >> return Int
    ERel expr1 op expr2 ->
        if op == EQU || op == NE then do
            t1 <- checkExpr expr1
            t2 <- checkExpr expr2
            trac <- asks trace
            if t1 == t2 then return Bool
            else throwError $ ETypeMismatch x t2 t1 trac
        else checkOp expr1 expr2 Int >> return Bool
    EAnd expr1 expr2 -> checkOp expr1 expr2 Bool >> return Bool
    EOr expr1 expr2 -> checkOp expr1 expr2 Bool >> return Bool
    where
    checkOp expr1 expr2 t = do
        t1 <- checkExpr expr1
        t2 <- checkExpr expr2
        trac <- asks trace
        if t1 == t && t2 == t then return ()
        else throwError $ ETypeMismatch x (if t1 == t then t2 else t1) t trac

initialTEnv :: TEnv
initialTEnv = Map.fromList [(Ident "printInt", Fun Void [Int]),
    (Ident "printString", Fun Void [Str]),
    (Ident "error", Fun Void []),
    (Ident "readInt", Fun Int []),
    (Ident "readString", Fun Str [])]

initialREnv :: TEnv -> REnv
initialREnv symbols = REnv symbols (Trace (FnDef Void (Ident "") [] (Block [])) [] Nothing)

initialState :: SEnv
initialState = Map.empty

argsTypes :: TopDef -> [Arg] -> Either Exception [Type]
argsTypes td args = reverse <$> fst <$> foldM (\(acc, set) (Arg t ident) ->
    if Set.member ident set then throwError (ERepeatedArgName ident td)
    else return (t : acc, Set.insert ident set)) ([], Set.empty) args

getSymbols :: Program -> TEnv -> Either Exception TEnv
getSymbols (Program topdefs) initialSym =  do
    res <- foldM addf initialSym topdefs
    if not (Map.member (Ident "main") res) then
        throwError ENoMain
    else return res
    where addf env topdef@(FnDef t ident args _) =
            if Map.member ident env then throwError (ERepeatedFun topdef)
            else do
                at <- argsTypes topdef args
                return $ Map.insert ident (Fun t at) env

runCheckProgram :: Program -> Either Exception TEnv
runCheckProgram program = do
    symbols <- getSymbols program initialTEnv
    evalStateT (runReaderT (checkProgram program) (initialREnv symbols))  initialState
    return symbols

