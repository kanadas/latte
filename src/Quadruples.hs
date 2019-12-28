module Quadruples where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.DList(DList, singleton)
import Data.Sort
import Control.Monad.State
import Control.Monad.Writer

import qualified AbsLatte as AL(MulOp(..), RelOp(..))
import AbsLatte(AddOp(..), Stmt(..), Item(..), Expr(..), Ident(..), Block(..))

newtype Variable = Variable Int
    deriving (Eq, Ord)

newtype Label = Label Int
    deriving (Eq, Ord)

data Val = Var Variable | VInt Integer | VBool Bool | VString String | VVoid
    deriving (Eq, Ord)

data Op
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    | And
    | Or
    | LTH
    | LE
    | GTH
    | GE
    | EQU
    | NE
    | Concat

data Quadruple
    = QAss Val Val
    | QOp Val Val Op Val
    | QNeg Val Val
    | QNot Val Val
    | QIf Val Label
    | QIfNot Val Label
    | QJmp Label
    | QLabel Label
    | QPush Val
    | QCall Val Ident
    | QRet Val
    | QRetV

type VEnv = Map.Map Ident Val
data QState = QState {venv :: VEnv, vars :: Int, labels :: Int}
type Result a = StateT QState (Writer (DList Quadruple)) a

liftVEnv :: (VEnv -> VEnv) -> QState -> QState
liftVEnv f s = s{venv = f (venv s)}

liftVars :: (Int -> Int) -> QState -> QState
liftVars f s = s{vars = f (vars s)}

liftLabels :: (Int -> Int) -> QState -> QState
liftLabels f s = s{labels = f (vars s)}

incVars :: Result Val
incVars = Var <$> Variable <$> (modify (liftVars (+1)) >> gets vars)

incLabels :: Result Label
incLabels = Label <$> (modify (liftLabels (+1)) >> gets labels)

convertBlock :: Block -> Result ()
convertBlock (Block stmts) = do
    env <- gets venv
    mapM_ convertStmt stmts
    modify $ liftVEnv (\_ -> env)

convertStmt :: Stmt -> Result ()
convertStmt x = case x of
    Empty -> return ()
    BStmt block -> convertBlock block
    Decl _ items -> mapM_ convertItem items
    Ass ident expr -> do
        r <- convertExpr expr
        v <- gets $ (Map.! ident).venv
        tell $ singleton $ QAss v r
    Incr ident -> do
        v <- gets $ (Map.! ident).venv
        tell $ singleton $ QOp v v Add (VInt 1)
    Decr ident -> do
        v <- gets $ (Map.! ident).venv
        tell $ singleton $ QOp v v Sub (VInt 1)
    Ret expr -> do
        v <- convertExpr expr
        tell $ singleton $ QRet v
    VRet -> tell $ singleton QRetV
    Cond expr stmt -> do
        v <- convertExpr expr
        l <- incLabels
        tell $ singleton $ QIfNot v l
        convertBlock $ Block [stmt]
        tell $ singleton $ QLabel l
    CondElse expr stmt1 stmt2 -> do
        v <- convertExpr expr
        lelse <- incLabels
        lend <- incLabels
        tell $ singleton $ QIfNot v lelse
        convertBlock $ Block [stmt1]
        tell $ singleton $ QJmp lend
        tell $ singleton $ QLabel lelse
        convertBlock $ Block [stmt2]
        tell $ singleton $ QLabel lend
    While expr stmt -> do
        lwhile <- incLabels
        lcond <- incLabels
        tell $ singleton $ QJmp lcond
        tell $ singleton $ QLabel lwhile
        convertBlock $ Block [stmt]
        tell $ singleton $ QLabel lcond
        v <- convertExpr expr
        tell $ singleton $ QIf v lwhile
    SExp _ -> return () --I think all expressions are immutable

convertItem :: Item -> Result ()
convertItem x = case x of
    NoInit ident -> do
        v <- incVars
        modify $ liftVEnv $ Map.insert ident v
    Init ident expr -> do
        r <- convertExpr expr
        v <- incVars
        modify $ liftVEnv $ Map.insert ident v
        tell $ singleton $ QAss v r

--Returns result variable of subexpression
convertExpr :: Expr -> Result Val
convertExpr x = case x of
    EVar ident -> gets $ (Map.! ident).venv
    ELitInt int-> return $ VInt int
    ELitTrue -> return $ VBool True
    ELitFalse -> return $ VBool False
    EApp ident exprs -> do
        mapM_ (\expr -> convertExpr expr >>= (\v -> tell $ singleton $ QPush v)) (reverse exprs)
        v <- incVars
        tell $ singleton $ QCall v ident
        return v
    EString string -> return $ VString string
    Neg expr -> do
        v <- convertExpr expr
        nv <- incVars
        tell $ singleton $ QNeg nv v
        return nv
    Not expr -> do
        v <- convertExpr expr
        nv <- incVars
        tell $ singleton $ QNot nv v
        return nv
    EMul expr1 mulop expr2 -> convertOp expr1 (convertMulOp mulop) expr2
    EAdd expr1 addop expr2 -> convertOp expr1 (convertAddOp addop) expr2
    ERel expr1 relop expr2 -> convertOp expr1 (convertRelOp relop) expr2
    EAnd expr1 expr2 -> convertOp expr1 And expr2
    EOr expr1 expr2 -> convertOp expr1 Or expr2
    where
    convertOp e1 op e2 = do
        v1 <- convertExpr e1
        v2 <- convertExpr e2
        nv <- incVars
        tell $ singleton $ QOp nv v1 op v2
        return nv


convertAddOp :: AddOp -> Op
convertAddOp x = case x of
  Plus -> Add
  Minus -> Sub

convertMulOp :: AL.MulOp -> Op
convertMulOp x = case x of
  AL.Times -> Mul
  AL.Div -> Div
  AL.Mod -> Mod

convertRelOp :: AL.RelOp -> Op
convertRelOp x = case x of
  AL.LTH -> LTH
  AL.LE -> LE
  AL.GTH -> GTH
  AL.GE -> GE
  AL.EQU -> EQU
  AL.NE -> NE

type Graph = Map.Map Variable [Variable]
type ListGraph = [(Variable, [Variable])]
type Colloring = Map.Map Variable Int

getVariables :: Quadruple -> [Variable]
getVariables q = case q of
    QAss v1 v2 ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        case v2 of Var v -> v:r1; _ -> r1
    QOp v1 v2 _ v3 ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        let r2 = case v2 of Var v -> v:r1; _ -> [] in
        case v3 of Var v -> v:r2; _ -> r2
    QNeg v1 v2 ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        case v2 of Var v -> v:r1; _ -> r1
    QNot v1 v2 ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        case v2 of Var v -> v:r1; _ -> r1
    QIf (Var v) _ -> [v]
    QIfNot (Var v) _ -> [v]
    QPush (Var v) -> [v]
    QCall (Var v) _ -> [v]
    QRet (Var v) -> [v]
    _ -> []

removeDups :: Ord a => [a] -> [a]
removeDups l = snd $ foldl f (Set.empty, []) l where
    f (s, a) v = if Set.member v s then (s, a) else (Set.insert v s, v:a)

collisionGraph :: [Quadruple] -> ListGraph
collisionGraph quads =
    let variables = removeDups $ foldl (\acc q -> (getVariables q) ++ acc) [] quads in
    foldl foldVars [] variables where
        foldVars acc v =  (v, (removeDups $ foldl foldQuads [] quads)) : acc where
            foldQuads a q = if elem v qv then (filter (/= v) qv) ++ a else a where
                qv = getVariables q

graphColloring :: ListGraph -> (Colloring, Int)
graphColloring g =
    orderedGraphColloring (sortOn (\(_, l) -> length l) g)


orderedGraphColloring :: ListGraph -> (Colloring, Int)
orderedGraphColloring g = foldl foldGraph (Map.empty, 0) g where
    foldGraph (coloring, nc) (v, l) =
        (Map.insert v color coloring, if color < nc then nc else nc + 1) where
        color = mexSorted 0 (sort (map (coloring Map.!) (filter (`Map.member` coloring) l))) where
            mexSorted n (x:xs) = if x == n then mexSorted (n+1) xs else n
            mexSorted n [] = n

nextUse :: Variable -> [Quadruple] -> Maybe Int
nextUse v q = nextUseAcum v q 1

nextUseAcum :: Variable -> [Quadruple] -> Int -> Maybe Int
nextUseAcum _ [] _ = Nothing
nextUseAcum v (x:xs) a = if elem v (getVariables x) then Just a else nextUseAcum v xs (a+1)

