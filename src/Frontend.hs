{-# LANGUAGE FlexibleContexts #-}
module Frontend where

--import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans.Reader
import Control.Monad.State.Lazy
import qualified Data.Map.Strict as Map

import AbsLatte

data Exception = 
      ERepeatedFun TopDef
    | ENotReturning TopDef
    | EUnknownVar Ident Trace
    | EUnknownFun Ident Trace
    | EArgMismatch Type Type Trace
    | EWrongArgCnt Trace
    | ENotAFun Ident Type Trace
    | ETypeMismatch Expr Type Type Trace
    | EDoubleDecl Ident Trace
    | ENotImplemented
    deriving Show

type TEnv = Map.Map Ident Type

data Trace = Trace { tracFun :: TopDef, tracStmts :: [Stmt], tracExpr :: Expr }
    deriving Show

data REnv = REnv { tenv :: TEnv, trace :: Trace }
type SEnv = TEnv
type Result a = ReaderT REnv (StateT SEnv (Either Exception)) a

appendTraceStmt :: Stmt -> REnv -> REnv
appendTraceStmt stmt (REnv x tr) = REnv x tr{tracStmts = stmt : (tracStmts tr)}

setTraceExpr :: Expr -> REnv -> REnv
setTraceExpr expr (REnv x tr) = REnv x tr{tracExpr = expr}

getCombEnv :: Result TEnv
getCombEnv = do
    lenv <- get
    asks $ (Map.union lenv).tenv   

getSymbols :: (MonadError Exception m) => Program -> m TEnv
getSymbols (Program topdefs) = 
    foldM addf Map.empty topdefs
    where addf env topdef@(FnDef t ident args _) = 
            if Map.member ident env then throwError (ERepeatedFun topdef)
            else return $ Map.insert ident (Fun t (argsTypes args)) env

argsTypes :: [Arg] -> [Type]
argsTypes args = foldr (\(Arg t _) acc -> t : acc) [] args

checkProgram :: Program -> Result ()
checkProgram program@(Program topdefs) = do
    symbols <- getSymbols program
    local (\e -> e{tenv = symbols}) (mapM_ checkTopDef topdefs)

checkTopDef :: TopDef -> Result ()
checkTopDef x = case x of
    FnDef t _ _ block -> do
        trac <- asks trace
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
    Decl t items -> mapM_ (checkItem x t) items >> return False
    Ass ident expr -> do
        te <- local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr)
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just t -> if t == te then return False 
                else throwError $ ETypeMismatch expr te t trac
            Nothing -> throwError $ EUnknownVar ident trac
    Incr ident -> do
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just Int -> return False
            Just t -> throwError $ ETypeMismatch (EVar ident) t Int trac
            Nothing -> throwError $ EUnknownVar ident trac
    Decr ident -> do
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just Int -> return False
            Just t -> throwError $ ETypeMismatch (EVar ident) t Int trac
            Nothing -> throwError $ EUnknownVar ident trac
    Ret expr -> do
        te <- local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr)
        trac <- asks trace
        case tracFun trac of
            FnDef t _ _ _ -> if t == te then return True 
                else throwError $ ETypeMismatch expr te t trac
    VRet -> do
        trac <- asks trace
        case tracFun trac of
            FnDef t ident _ _ -> if t == Void then return True 
                else throwError $ ETypeMismatch (EVar ident) t Void trac
    Cond expr stmt -> do
        te <- local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr)
        trac <- asks trace
        if te == Bool then do 
            env <- getCombEnv
            stat <- get
            put Map.empty
            rets <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkStmt stmt)
            put stat
            if expr == ELitTrue && rets then return True else return False
        else throwError $ ETypeMismatch expr te Bool trac
    CondElse expr stmt1 stmt2 -> do
        te <- local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr)
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
        else throwError $ ETypeMismatch expr te Bool trac
    While expr stmt -> do
        te <- local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr)
        trac <- asks trace
        if te == Bool then do 
            env <- getCombEnv
            stat <- get
            put Map.empty
            rets <- local ((\e -> e{tenv = env}).(appendTraceStmt x)) (checkStmt stmt)
            put stat
            if expr == ELitTrue || rets then return True
            else return False
        else throwError $ ETypeMismatch expr te Bool trac
    SExp expr -> local ((appendTraceStmt x).(setTraceExpr expr)) (checkExpr expr) >> return False

checkItem :: Stmt -> Type -> Item -> Result ()
checkItem stmt t x = case x of
    NoInit ident -> do
        env <- get
        trac <- asks trace
        if Map.member ident env then throwError $ EDoubleDecl ident trac
        else modify (Map.insert ident t)
    Init ident expr -> do
        trac <- asks trace
        te <- local ((appendTraceStmt stmt).(setTraceExpr expr)) (checkExpr expr)
        if te == t then do
            env <- get
            if Map.member ident env then throwError $ EDoubleDecl ident trac
            else modify (Map.insert ident t)
        else throwError $ ETypeMismatch expr te t trac

--localCheckExpr :: Stmt -> Expr -> Result Type
--localCheckExpr s x = do
--    env <- getCombEnv
--    local (\renv -> renv {tenv = env, 

checkExpr :: Expr -> Result Type
checkExpr x = case x of
    EVar ident -> do
        env <- getCombEnv
        trac <- asks trace
        case env Map.!? ident of
            Just t -> return t
            Nothing -> throwError $ EUnknownVar ident trac
    ELitInt _ -> return Int
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
    EMul expr1 _ expr2 -> checkOp expr1 expr2 Int
    EAdd expr1 _ expr2 -> checkOp expr1 expr2 Int
    ERel expr1 _ expr2 -> checkOp expr1 expr2 Int
    EAnd expr1 expr2 -> checkOp expr1 expr2 Int
    EOr expr1 expr2 -> checkOp expr1 expr2 Int
    where 
    checkOp expr1 expr2 t = do
        t1 <- checkExpr expr1
        t2 <- checkExpr expr2
        trac <- asks trace
        if t1 == t && t2 == t then return t 
        else throwError $ ETypeMismatch x (if t1 == t then t2 else t1) t trac

