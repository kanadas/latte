module Compiler where

import AbsLatte
import ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

compileProgram :: Program -> Result
compileProgram x = case x of
  Program topdefs -> failure x

compileTopDef :: TopDef -> Result
compileTopDef x = case x of
  FnDef type_ ident args block -> failure x

compileArg :: Arg -> Result
compileArg x = case x of
  Arg type_ ident -> failure x

compileBlock :: Block -> Result
compileBlock x = case x of
  Block stmts -> failure x

compileStmt :: Stmt -> Result
compileStmt x = case x of
  Empty -> failure x
  BStmt block -> failure x
  Decl type_ items -> failure x
  Ass ident expr -> failure x
  Incr ident -> failure x
  Decr ident -> failure x
  Ret expr -> failure x
  VRet -> failure x
  Cond expr stmt -> failure x
  CondElse expr stmt1 stmt2 -> failure x
  While expr stmt -> failure x
  SExp expr -> failure x

compileItem :: Item -> Result
compileItem x = case x of
  NoInit ident -> failure x
  Init ident expr -> failure x

compileType :: Type -> Result
compileType x = case x of
  Int -> failure x
  Str -> failure x
  Bool -> failure x
  Void -> failure x
  Fun type_ types -> failure x

compileExpr :: Expr -> Result
compileExpr x = case x of
  EVar ident -> failure x
  ELitInt integer -> failure x
  ELitTrue -> failure x
  ELitFalse -> failure x
  EApp ident exprs -> failure x
  EString string -> failure x
  Neg expr -> failure x
  Not expr -> failure x
  EMul expr1 mulop expr2 -> failure x
  EAdd expr1 addop expr2 -> failure x
  ERel expr1 relop expr2 -> failure x
  EAnd expr1 expr2 -> failure x
  EOr expr1 expr2 -> failure x

compileAddOp :: AddOp -> Result
compileAddOp x = case x of
  Plus -> failure x
  Minus -> failure x

compileMulOp :: MulOp -> Result
compileMulOp x = case x of
  Times -> failure x
  Div -> failure x
  Mod -> failure x

compileRelOp :: RelOp -> Result
compileRelOp x = case x of
  LTH -> failure x
  LE -> failure x
  GTH -> failure x
  GE -> failure x
  EQU -> failure x
  NE -> failure x

compileIdent :: Ident -> Result
compileIdent x = case x of
  Ident string -> failure x


