module Quadruples(
    Variable(..),
    Label(..),
    Val(..),
    Op(..),
    Quadruple(..),
    convertTopDef,
    Graph,
    ListGraph,
    Coloring,
    collisionGraph,
    graphColoring,
    getAllVariables,
    getVariables
) where

--TODO change arg clique to sth better

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.DList(DList, singleton, toList, fromList)
import Data.Sort
import Control.Monad.State
import Control.Monad.Writer

import AbsLatte
import Frontend(TEnv)

newtype Variable = Variable Int
    deriving (Eq, Ord, Show)

newtype Label = Label Int
    deriving (Eq, Ord)

instance Show Label where
    show (Label l) = "_l" ++ show l

data Val = Var Variable | VInt Integer | VBool Bool | VString String | VStrRef Variable
    deriving (Eq, Show)

data Op
    = OAdd
    | OSub
    | OMul
    | ODiv
    | OMod
    | OLTH
    | OLE
    | OGTH
    | OGE
    | OEQU
    | ONE
    | OConcat
    deriving (Eq, Show)

data Quadruple
    = QAss Val Val
    | QOp Val Val Op Val
    | QNeg Val Val
    | QNot Val Val
    | QIf Val Op Val Label
    | QJmp Label
    | QLabel Label
    | QCall Val Ident [Val]
    | QRet Val
    | QRetV
    deriving Eq

type VEnv = Map.Map Ident Val
data QState = QState {
    venv :: VEnv
    , vars :: Int
    , labels :: Int
    , if_labels :: Maybe (Label, Label)
    , tenv :: TEnv}
type Result a = StateT QState (Writer (DList Quadruple)) a

liftVEnv :: (VEnv -> VEnv) -> QState -> QState
liftVEnv f s = s{venv = f (venv s)}

liftVars :: (Int -> Int) -> QState -> QState
liftVars f s = s{vars = f (vars s)}

liftLabels :: (Int -> Int) -> QState -> QState
liftLabels f s = s{labels = f (labels s)}

liftIfLabels :: (Maybe (Label, Label) -> Maybe (Label, Label)) -> QState -> QState
liftIfLabels f s = s{if_labels = f (if_labels s)}

incVars :: Result Val
incVars = Var <$> Variable <$> (modify (liftVars (+1)) >> gets vars)

incLabels :: Result Label
incLabels = Label <$> (modify (liftLabels (+1)) >> gets labels)

convertTopDef :: Int -> TEnv -> TopDef -> ([Quadruple], Coloring)
convertTopDef fst_label types (FnDef t _ args block) =
    let (argEnv, nargs) = foldl (\(acc, n) (Arg _ arg) ->
            (Map.insert arg (Var (Variable n)) acc, n + 1)) (Map.empty, 0) args in
    let res = toList $ execWriter (
            evalStateT (convertBlock block) (QState argEnv nargs fst_label Nothing types)) in
    let res2 = if t == Void && (last res /= QRetV) then res ++ [QRetV] else res in
    let (coloring, _) = (graphColoring . (collisionGraph nargs)) res in
    let res3 = filter filterNotUsedVars res2 where
        filterNotUsedVars q = case q of
            QAss (Var v) _ -> Map.member v coloring
            QOp (Var v) _ _ _ -> Map.member v coloring
            QNeg (Var v) _ -> Map.member v coloring
            QNot (Var v) _ -> Map.member v coloring
            _ -> True in
    (res3, coloring)

convertBlock :: Block -> Result ()
convertBlock (Block stmts) = do
    env <- gets venv
    mapM_ convertStmt stmts
    modify $ liftVEnv (\_ -> env)

convertStmt :: Stmt -> Result ()
convertStmt x = case x of
    Empty -> return ()
    BStmt block -> convertBlock block
    Decl t items -> mapM_ (convertItem t) items
    Ass ident expr -> do
        r <- convertExpr expr
        v <- gets $ (Map.! ident).venv
        tell $ singleton $ QAss v r
    Incr ident -> do
        v <- gets $ (Map.! ident).venv
        tell $ singleton $ QOp v v OAdd (VInt 1)
    Decr ident -> do
        v <- gets $ (Map.! ident).venv
        tell $ singleton $ QOp v v OSub (VInt 1)
    Ret expr -> do
        v <- convertExpr expr
        tell $ singleton $ QRet v
    VRet -> tell $ singleton QRetV
    Cond expr stmt -> do
        lthen <- incLabels
        lelse <- incLabels
        modify $ liftIfLabels (\_ -> Just (lthen, lelse))
        _ <- convertExpr expr
        modify $ liftIfLabels (\_ -> Nothing)
        tell $ singleton $ QLabel lthen
        convertBlock $ Block [stmt]
        tell $ singleton $ QLabel lelse
    CondElse expr stmt1 stmt2 -> do
        lthen <- incLabels
        lelse <- incLabels
        lend <- incLabels
        modify $ liftIfLabels (\_ -> Just (lthen, lelse))
        _ <- convertExpr expr
        modify $ liftIfLabels (\_ -> Nothing)
        tell $ singleton $ QLabel lthen
        convertBlock $ Block [stmt1]
        tell $ singleton $ QJmp lend
        tell $ singleton $ QLabel lelse
        convertBlock $ Block [stmt2]
        tell $ singleton $ QLabel lend
    While expr stmt -> do
        lwhile <- incLabels
        lcond <- incLabels
        lend <- incLabels
        tell $ singleton $ QJmp lcond
        tell $ singleton $ QLabel lwhile
        convertBlock $ Block [stmt]
        tell $ singleton $ QLabel lcond
        modify $ liftIfLabels (\_ -> Just (lwhile, lend))
        _ <- convertExpr expr
        modify $ liftIfLabels (\_ -> Nothing)
        tell $ singleton $ QLabel lend
    SExp expr -> convertExpr expr >> return ()

convertItem :: Type -> Item -> Result ()
convertItem t x = case x of
    NoInit ident -> do
        v <- incVars
        modify $ liftVEnv $ Map.insert ident v
        tell $ singleton $ QAss v initial where
            initial = case t of
                Int -> VInt 0
                Str -> VString ""
                Bool -> VBool False
                _ -> error "bad type"
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
    ELitTrue -> do
        in_if <- gets if_labels
        case in_if of
            Nothing -> return ()
            Just (ltrue, _) -> tell $ singleton $ QJmp ltrue
        return $ VBool True
    ELitFalse -> do
        in_if <- gets if_labels
        case in_if of
            Nothing -> return ()
            Just (_, lfalse) -> tell $ singleton $ QJmp lfalse
        return $ VBool False
    EApp ident exprs -> do
        args <- foldM (\acc expr -> (:acc) <$> convertExpr expr) [] (reverse exprs)
        ret_t <- (Map.! ident) <$> gets tenv
        v <- if ret_t == Str then
                VStrRef <$> Variable <$> (modify (liftVars (+1)) >> gets vars)
            else incVars
        tell $ singleton $ QCall v ident args
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
    ERel expr1 relop expr2 -> do
        in_if <- gets if_labels
        case in_if of
            Nothing -> convertOp expr1 (convertRelOp relop) expr2
            Just (ltrue, lfalse) -> do
                v1 <- convertExpr expr1
                v2 <- convertExpr expr2
                tell $ singleton $ QIf v1 (convertRelOp relop) v2 ltrue
                tell $ singleton $ QJmp lfalse
                return v2
    EAnd expr1 expr2 -> do
        in_if <- gets if_labels
        case in_if of
            Nothing -> do
                ltrue1 <- incLabels
                ltrue2 <- incLabels
                lfalse <- incLabels
                lend <- incLabels
                nv <- incVars
                modify $ liftIfLabels (\_ -> Just (ltrue1, lfalse))
                _ <- convertExpr expr1
                tell $ singleton $ QLabel ltrue1
                modify $ liftIfLabels (\_ -> Just (ltrue2, lfalse))
                _ <- convertExpr expr2
                modify $ liftIfLabels (\_ -> Nothing)
                tell $ fromList [QLabel ltrue2,
                                QAss nv (VBool True),
                                QJmp lend,
                                QLabel lfalse,
                                QAss nv (VBool False),
                                QLabel lend]
                return nv
            Just (ltrue, lfalse) -> do
                lmid <- incLabels
                modify $ liftIfLabels (\_ -> Just (lmid, lfalse))
                _ <- convertExpr expr1
                modify $ liftIfLabels (\_ -> Just (ltrue, lfalse))
                convertExpr expr2
    EOr expr1 expr2 ->  do
        in_if <- gets if_labels
        case in_if of
            Nothing -> do
                lfalse1 <- incLabels
                lfalse2 <- incLabels
                ltrue <- incLabels
                lend <- incLabels
                nv <- incVars
                modify $ liftIfLabels (\_ -> Just (ltrue, lfalse1))
                _ <- convertExpr expr1
                tell $ singleton $ QLabel lfalse1
                modify $ liftIfLabels (\_ -> Just (ltrue, lfalse2))
                _ <- convertExpr expr2
                modify $ liftIfLabels (\_ -> Nothing)
                tell $ fromList [QLabel lfalse2,
                                QAss nv (VBool False),
                                QJmp lend,
                                QLabel ltrue,
                                QAss nv (VBool True),
                                QLabel lend]
                return nv
            Just (ltrue, lfalse) -> do
                    lmid <- incLabels
                    modify $ liftIfLabels (\_ -> Just (ltrue, lmid))
                    _ <- convertExpr expr1
                    modify $ liftIfLabels (\_ -> Just (ltrue, lfalse))
                    convertExpr expr2
    where
    convertOp e1 op e2 = do
        v1 <- convertExpr e1
        v2 <- convertExpr e2
        nv <- incVars
        let nop = if op == OAdd && (isString v1) then OConcat else op
        tell $ singleton $ QOp nv v1 nop v2
        return nv

isString :: Val -> Bool
isString x = case x of
    VString _ -> True
    VStrRef _ -> True
    _ -> False

convertAddOp :: AddOp -> Op
convertAddOp x = case x of
  Plus -> OAdd
  Minus -> OSub

convertMulOp :: MulOp -> Op
convertMulOp x = case x of
  Times -> OMul
  Div -> ODiv
  Mod -> OMod

convertRelOp :: RelOp -> Op
convertRelOp x = case x of
  LTH -> OLTH
  LE -> OLE
  GTH -> OGTH
  GE -> OGE
  EQU -> OEQU
  NE -> ONE

type Graph = Map.Map Variable [Variable]
type ListGraph = [(Variable, [Variable])]
type Coloring = Map.Map Variable Int

getVariables :: Quadruple -> [Variable]
getVariables q = case q of
    QAss _ (Var v) -> [v]
    QOp _ v1 _ v2 ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        case v2 of Var v -> v:r1; _ -> r1
    QNeg _ (Var v) -> [v]
    QNot _ (Var v) -> [v]
    QIf v1 _ v2 _ ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        case v2 of Var v -> v:r1; _ -> r1
    QCall _ _ args -> foldl (\acc arg -> case arg of Var v -> v:acc; _ -> acc) [] args
    QRet (Var v) -> [v]
    _ -> []

getAllVariables :: Quadruple -> [Variable]
getAllVariables q = case q of
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
    QIf v1 _ v2 _ ->
        let r1 = case v1 of Var v -> [v]; _ -> [] in
        case v2 of Var v -> v:r1; _ -> r1
    QCall val _ args -> foldl (\acc arg -> case arg of Var v -> v:acc; _ -> acc) [] (val:args)
    QRet (Var v) -> [v]
    _ -> []



removeDups :: Ord a => [a] -> [a]
removeDups l = snd $ foldl f (Set.empty, []) l where
    f (s, a) v = if Set.member v s then (s, a) else (Set.insert v s, v:a)

collisionGraph :: Int -> [Quadruple] -> ListGraph
collisionGraph n_args quads =
    let variables = removeDups $ foldl (\acc q -> (getVariables q) ++ acc) [] quads in
    let var_no_args = filter (\(Variable n) -> n >= n_args) variables in
    let arg_cluque = map (\n -> ((Variable n), map Variable (filter (/= n) [0..n_args - 1])))
            [0 .. n_args - 1] in
    foldl foldVars arg_cluque var_no_args where
        foldVars acc v =  (v, (removeDups $ foldl foldQuads [] quads)) : acc where
            foldQuads a q = if elem v qv then (filter (/= v) qv) ++ a else a where
                qv = getVariables q

graphColoring :: ListGraph -> (Coloring, Int)
graphColoring g =
    orderedGraphColoring (sortOn (\(_, l) -> length l) g)


orderedGraphColoring :: ListGraph -> (Coloring, Int)
orderedGraphColoring g = foldl foldGraph (Map.empty, 0) g where
    foldGraph (coloring, nc) (v, l) =
        (Map.insert v color coloring, if color < nc then nc else nc + 1) where
        color = mexSorted 0 (sort (map (coloring Map.!) (filter (`Map.member` coloring) l))) where
            mexSorted n (x:xs) = if x == n then mexSorted (n+1) xs else n
            mexSorted n [] = n

