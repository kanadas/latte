{-# LANGUAGE CPP #-} --for ifdef
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
    getUsedVariables
) where

--TODO optimizations:
--remove unused labels
--remove blocks without in edges (besides 0 block)
--remove unused variables

import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set
import Data.DList(DList, singleton, toList, fromList)
import Data.Sort
--import Data.List
import Control.Monad.State
import Control.Monad.Writer

import AbsLatte
import Frontend(TEnv)

import qualified Debug.Trace
import qualified Debug.Pretty.Simple

trace :: String -> a -> a
pTrace :: String -> a -> a
#ifdef DEBUG
trace = Debug.Trace.trace
pTrace = Debug.Pretty.Simple.pTrace
#else
trace _ b = b
pTrace _ b = b
#endif

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
    | QCallV Ident [Val]
    | QRet Val
    | QRetV
    deriving (Eq, Show)

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

incVars :: Bool -> Result Val
incVars b = (if b then VStrRef else Var) <$> Variable <$> (modify (liftVars (+1)) >> gets vars)

incLabels :: Result Label
incLabels = Label <$> (modify (liftLabels (+1)) >> gets labels)

convertTopDef :: Int -> TEnv -> TopDef -> ([Quadruple], Coloring, Int)
convertTopDef _ _ (FnDef _ x _ _) | trace ("convertTopDef: " ++ show x) False = undefined
convertTopDef fst_label types (FnDef _ _ args block) =
    let (argEnv, nargs) = foldl (\(acc, n) (Arg t arg) ->
            (Map.insert arg ((if t == Str then VStrRef else Var) (Variable n)) acc, n + 1))
            (Map.empty, 0) args in
    let res = toList $ execWriter (
            evalStateT (convertBlock block) (QState argEnv nargs fst_label Nothing types)) in
    let res2 = if res == [] then [QRetV] else case last res of
            QRet _ -> res --TODO remove unreachable blocks
            QRetV  -> res
            _ -> res ++ [QRetV] in

    let trace_res = trace ("Quadruples:\n" ++ unlines (map show res2)) res2 in

    let ssaGraph = toSSA nargs (computeFlow trace_res) in
    --TODO optimizations
    let (coloring, ncolors) = graphColoring (collisionGraph ssaGraph) in
    let res3 = foldr (\(_, node) acc -> (code node) ++ acc)
            [] (IntMap.assocs (graph_nodes ssaGraph)) in
    --let res3 = filter filterNotUsedVars res2 where
    --    filterNotUsedVars q = case q of --TODO test it
    --        QAss (Var v) _ -> Map.member v coloring
    --        QOp (Var v) _ _ _ -> Map.member v coloring
    --        QNeg (Var v) _ -> Map.member v coloring
    --        QNot (Var v) _ -> Map.member v coloring
    --        _ -> True in
    --let _ = trace (show res3) False in
    (res3, coloring, ncolors)

convertBlock :: Block -> Result ()
convertBlock (Block stmts) = do
    env <- gets venv
    mapM_ convertStmt stmts
    modify $ liftVEnv (\_ -> env)

convertStmt :: Stmt -> Result ()
convertStmt x | trace ("convertStmt: " ++ show x) False = undefined
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
        v <- incVars (t == Str)
        modify $ liftVEnv $ Map.insert ident v
        tell $ singleton $ QAss v initial where
            initial = case t of
                Int -> VInt 0
                Str -> VString ""
                Bool -> VBool False
                _ -> error "bad type"
    Init ident expr -> do
        r <- convertExpr expr
        v <- incVars (t == Str)
        modify $ liftVEnv $ Map.insert ident v
        tell $ singleton $ QAss v r

--Returns result variable of subexpression
convertExpr :: Expr -> Result Val
convertExpr x | trace ("convertExpr: " ++ show x) False = undefined
convertExpr x = case x of
    EVar ident -> do
        v <- gets $ (Map.! ident).venv
        in_if <- gets if_labels
        case in_if of
            Nothing -> return ()
            Just (ltrue, lfalse) ->
                tell $ fromList [QIf v OEQU (VBool True) ltrue
                                , QJmp lfalse]
        return v
    ELitInt int-> return $ VInt int
    ELitTrue -> return $ VBool True
    ELitFalse -> return $ VBool False
    EApp ident exprs -> do
        args <- foldM (\acc expr -> (:acc) <$> convertExpr expr) [] (reverse exprs)
        ret_t <- (Map.! ident) <$> gets tenv
        in_if <- gets if_labels
        modify $ liftIfLabels (\_ -> Nothing)
        case ret_t of
            Fun Void _ ->
                tell (singleton $ QCallV ident args) >> return (VInt 0)
            Fun t _ -> do
                v <- incVars (t == Str)
                tell $ singleton $ QCall v ident args
                case in_if of
                    Nothing -> return ()
                    Just (ltrue, lfalse) ->
                        tell $ fromList [QIf v OEQU (VBool True) ltrue,
                                        QJmp lfalse]
                return v
            _ ->  error $ "not a function type: " ++ show ret_t
    EString string -> return $ VString string
    Neg expr -> do
        v <- convertExpr expr
        case v of
            VInt n -> return $ VInt (-n)
            _ -> do
                nv <- incVars False
                tell $ singleton $ QNeg nv v
                return nv
    Not expr -> do
        modify $ liftIfLabels (fmap (\(ltrue, lfalse) -> (lfalse, ltrue)))
        v <- convertExpr expr
        case v of
            VBool b -> return $ VBool (not b)
            _ -> do
                nv <- incVars False
                tell $ singleton $ QNot nv v
                return nv
    EMul expr1 mulop expr2 -> convertOp expr1 (convertMulOp mulop) expr2
    EAdd expr1 addop expr2 -> convertOp expr1 (convertAddOp addop) expr2
    ERel expr1 relop expr2 -> do
        in_if <- gets if_labels
        case in_if of
            Nothing -> convertOp expr1 (convertRelOp relop) expr2
            Just (ltrue, lfalse) -> do
                modify $ liftIfLabels (\_ -> Nothing)
                v1 <- convertExpr expr1
                v2 <- convertExpr expr2
                case getConstResult v1 (convertRelOp relop) v2 of
                    Just (VBool b) -> return $ VBool b
                    Nothing -> do
                        tell $ singleton $ QIf v1 (convertRelOp relop) v2 ltrue
                        tell $ singleton $ QJmp lfalse
                        case v1 of
                            Var _ -> return v1
                            VStrRef _ -> return v1
                            _ -> return v2
                    _ -> error "not boolean result"
    EAnd expr1 expr2 -> do
        in_if <- gets if_labels
        case in_if of
            Nothing -> do
                ltrue1 <- incLabels
                ltrue2 <- incLabels
                lfalse <- incLabels
                lend <- incLabels
                modify $ liftIfLabels (\_ -> Just (ltrue1, lfalse))
                v1 <- convertExpr expr1
                case v1 of
                    VBool b -> do
                        modify $ liftIfLabels (\_ -> Nothing)
                        if b then convertExpr expr2 else return v1
                    _ -> do
                        tell $ singleton $ QLabel ltrue1
                        modify $ liftIfLabels (\_ -> Just (ltrue2, lfalse))
                        nv <- incVars False
                        v2 <- convertExpr expr2
                        case v2 of
                            VBool False -> tell $ fromList [QLabel lfalse,
                                                            QAss nv (VBool False)]
                            _ -> tell $ fromList [QLabel ltrue2,
                                                QAss nv (VBool True),
                                                QJmp lend,
                                                QLabel lfalse,
                                                QAss nv (VBool False),
                                                QLabel lend]
                        modify $ liftIfLabels (\_ -> Nothing)
                        return nv
            Just (ltrue, lfalse) -> do
                lmid <- incLabels
                modify $ liftIfLabels (\_ -> Just (lmid, lfalse))
                v1 <- convertExpr expr1
                case v1 of
                    VBool False -> return v1
                    _ -> do
                        tell $ singleton $ QLabel lmid
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
                modify $ liftIfLabels (\_ -> Just (ltrue, lfalse1))
                v1 <- convertExpr expr1
                case v1 of
                    VBool b -> do
                        modify $ liftIfLabels (\_ -> Nothing)
                        if b then return v1 else convertExpr expr2
                    _ -> do
                        tell $ singleton $ QLabel lfalse1
                        modify $ liftIfLabels (\_ -> Just (ltrue, lfalse2))
                        nv <- incVars False
                        v2 <- convertExpr expr2
                        case v2 of
                            VBool True -> tell $ fromList [QLabel ltrue,
                                                            QAss nv (VBool True)]
                            _ -> tell $ fromList [QLabel lfalse2,
                                                QAss nv (VBool False),
                                                QJmp lend,
                                                QLabel ltrue,
                                                QAss nv (VBool True),
                                                QLabel lend]
                        modify $ liftIfLabels (\_ -> Nothing)
                        return nv
            Just (ltrue, lfalse) -> do
                    lmid <- incLabels
                    modify $ liftIfLabels (\_ -> Just (ltrue, lmid))
                    v1 <- convertExpr expr1
                    case v1 of
                        VBool True -> return v1
                        _ -> do
                            tell $ singleton $ QLabel lmid
                            modify $ liftIfLabels (\_ -> Just (ltrue, lfalse))
                            convertExpr expr2
    where
    getConstResult v1 op v2 = case (v1,v2) of
        (VInt n1, VInt n2) -> Just $ case op of
            OAdd -> VInt (n1 + n2)
            OSub -> VInt (n1 - n2)
            OMul -> VInt (n1 * n2)
            ODiv -> VInt (quot n1 n2)
            OMod -> VInt (mod n1 n2)
            OLTH -> VBool (n1 < n2)
            OLE -> VBool (n1 <= n2)
            OGTH -> VBool (n1 > n2)
            OGE -> VBool (n1 >= n2)
            OEQU -> VBool (n1 == n2)
            ONE -> VBool (n1 /= n2)
            _ -> error $ "not an int operation: " ++ show op
        (VBool b1, VBool b2) -> Just $ case op of
            OEQU -> VBool (b1 == b2)
            ONE -> VBool (b1 /= b2)
            _ -> error $ "not an bool operation: " ++ show op
        (VString s1, VString s2) -> Just $ case op of
            OEQU -> VBool (s1 == s2)
            ONE -> VBool (s1 /= s2)
            OConcat -> VString (s1 ++ s2)
            _ -> error $ "not an string operation: " ++ show op
        _ -> Nothing
    convertOp e1 op e2 = do
        v1 <- convertExpr e1
        v2 <- convertExpr e2
        let nop = if op == OAdd && (isString v1) then OConcat else op
        case getConstResult v1 nop v2 of
            Just v -> return v
            _ -> do
                nv <- incVars (isString v1)
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

type BlockId = Int
data SimpleBlock = SimpleBlock {bid :: BlockId
    , code :: [Quadruple]
    , pre_alive :: Set.Set Variable
    , post_alive :: Set.Set Variable
    , used :: Set.Set Variable
    , defined :: Set.Set Variable}
    deriving Show

data FlowGraph = FlowGraph {out_edges :: IntMap.IntMap [BlockId]
    , in_edges :: IntMap.IntMap [BlockId]
    , graph_nodes :: IntMap.IntMap SimpleBlock}
    deriving Show

liftCode :: ([Quadruple] -> [Quadruple]) -> SimpleBlock -> SimpleBlock
liftCode f s = s{code = f (code s)}

--liftPreAlive :: ([Variable] -> [Variable]) -> SimpleBlock -> SimpleBlock
--liftPreAlive f s = s{pre_alive = f (pre_alive s)}

liftPostAlive :: (Set.Set Variable -> Set.Set Variable) -> SimpleBlock -> SimpleBlock
liftPostAlive f s = s{post_alive = f (post_alive s)}

liftUsed :: (Set.Set Variable -> Set.Set Variable) -> SimpleBlock -> SimpleBlock
liftUsed f s = s{used = f (used s)}

liftDefined :: (Set.Set Variable -> Set.Set Variable) -> SimpleBlock -> SimpleBlock
liftDefined f s = s{defined = f (defined s)}

liftOutEdges :: (IntMap.IntMap [BlockId] -> IntMap.IntMap [BlockId]) -> FlowGraph -> FlowGraph
liftOutEdges f s = s{out_edges = f (out_edges s)}

liftInEdges :: (IntMap.IntMap [BlockId] -> IntMap.IntMap [BlockId]) -> FlowGraph -> FlowGraph
liftInEdges f s = s{in_edges = f (in_edges s)}

liftNodes :: (IntMap.IntMap SimpleBlock -> IntMap.IntMap SimpleBlock) -> FlowGraph -> FlowGraph
liftNodes f s = s{graph_nodes = f (graph_nodes s)}

computeFlow :: [Quadruple] -> FlowGraph
computeFlow _ | trace "computeFlow" False = undefined
computeFlow nodes =
    let (fg, lmap) = runState (computeFlowAcc nodes
            (FlowGraph IntMap.empty IntMap.empty IntMap.empty) 0) Map.empty in
    computeAlive $ foldl (addEdges lmap) fg (graph_nodes fg)
    where
    computeFlowAcc :: [Quadruple] -> FlowGraph -> Int -> State (Map.Map Label Int) FlowGraph
    --computeFlowAcc (q:_) _ _ | trace ("computeFlowAcc: " ++ show q) False = undefined
    computeFlowAcc [] acc _ = return $ liftInEdges (IntMap.insert 0 []) acc
    computeFlowAcc (q:quads) acc n = do
        (qs, block) <- case q of
            QLabel l -> do
                modify $ (Map.insert l n)
                let sblock = SimpleBlock n [q] Set.empty Set.empty Set.empty Set.empty
                return $ computeSimpleBlock quads sblock
            _ -> let sblock = SimpleBlock n [] Set.empty Set.empty Set.empty Set.empty in
                return $ computeSimpleBlock (q:quads) sblock
        computeFlowAcc qs (liftNodes (IntMap.insert n block) acc) (n+1)
    computeSimpleBlock [] acc = ([], liftCode reverse acc)
    --computeSimpleBlock (q:_) acc | trace ("computeSimpleBlock: " ++ show q ++ "\n acc = " ++ show acc) False = undefined
    computeSimpleBlock (q:qs) acc =
        let nacc = liftDefined (Set.union (Set.fromList (getDefinedVariables q)))
                (liftUsed (Set.union (Set.fromList (
                filter (\v -> not (elem v (defined acc))) (getUsedVariables q)))) acc) in
        case q of
            QIf _ _ _ _ -> (qs, liftCode (reverse.(q:)) nacc)
            QJmp _ -> (qs, liftCode (reverse.(q:)) nacc)
            QLabel _ -> (q:qs, liftCode reverse nacc)
            QRet _ -> (qs, liftCode (reverse.(q:)) nacc)
            QRetV -> (qs, liftCode (reverse.(q:)) nacc)
            _ -> computeSimpleBlock qs (liftCode (q:) nacc)
    --addEdges _ _ simb | pTrace ("addEdges: " ++ show simb ++ "\n" ++ show (last (code simb))) False = undefined
    addEdges lmap fg simb =
        case last (code simb) of
                QIf _ _ _ label -> let edge = (lmap Map.! label) in
                    addEdge (bid simb) edge (
                        if edge /= bid simb + 1 then addEdge (bid simb) (bid simb + 1) fg
                        else fg)
                QJmp label -> addEdge (bid simb) (lmap Map.! label) fg
                QRet _ -> liftOutEdges (IntMap.insertWith (++) (bid simb) []) fg
                QRetV -> liftOutEdges (IntMap.insertWith (++) (bid simb) []) fg
                _ -> addEdge (bid simb) (bid simb + 1) fg
        where
        addEdge a b cfg =
                liftOutEdges (IntMap.insertWith (++) a [b]) (
                liftInEdges (IntMap.insertWith (++) b [a]) cfg)
    computeAlive :: FlowGraph -> FlowGraph
    --computeAlive fg | pTrace ("computeAlive: " ++ show fg) False = undefined
    computeAlive fg =
        let (nfg, chg) = foldl iterGraph (fg, False) (graph_nodes fg) in
        if chg then computeAlive nfg else nfg
        where
        iterGraph (acc, chg) node =
            let npost = foldl (\a nid -> Set.union (pre_alive ((graph_nodes acc) IntMap.! nid)) a)
                    Set.empty ((out_edges acc) IntMap.! (bid node)) in
            let npre = Set.union (used node) (npost Set.\\ (defined node)) in
            let nchg = chg || npre /= (pre_alive node) || npost /= (post_alive node) in
            let ngraph = liftNodes (IntMap.insert (bid node)
                    node{pre_alive = npre, post_alive = npost}) acc in
            (ngraph, nchg)

data SSAState = SSAState {
    var_map :: Map.Map Variable Variable
    , rev_map :: Map.Map Variable Variable
    , next_var :: Int}

liftVarMap :: (Map.Map Variable Variable -> Map.Map Variable Variable) -> SSAState -> SSAState
liftVarMap f s = s{var_map = f (var_map s)}

liftRevMap :: (Map.Map Variable Variable -> Map.Map Variable Variable) -> SSAState -> SSAState
liftRevMap f s = s{rev_map = f (rev_map s)}

liftNextVar :: (Int -> Int) -> SSAState -> SSAState
liftNextVar f s = s{next_var = f (next_var s)}

toSSA :: Int -> FlowGraph -> FlowGraph
toSSA nargs flow_graph =
    let argEnv = foldl (\acc n ->
            Map.insert (Variable n) (Variable n) acc) Map.empty [0 .. nargs-1] in
    let emptyFG = (FlowGraph (out_edges flow_graph) (in_edges flow_graph) IntMap.empty) in
    let (nfg, fstate) = runState (foldM blockToSSA emptyFG (graph_nodes flow_graph))
            (SSAState argEnv argEnv nargs) in
    elimPhi fstate nfg
    where
    blockToSSA :: FlowGraph -> SimpleBlock -> State SSAState FlowGraph
    blockToSSA cfg block = do
        npre <- if bid block /= 0 then
            foldM (\acc var -> do
                nv <- mapNewVar var
                return $ Set.insert nv acc) Set.empty (pre_alive block)
            else return $ pre_alive block
        (nquads, nused, ndef) <- foldM foldQuads ([], Set.empty, Set.empty) (code block)
        vmap <- gets var_map
        let npost = Set.map (vmap Map.!) (post_alive block)
        let nblock = SimpleBlock (bid block) (reverse nquads) npre npost nused ndef
        return $ liftNodes (IntMap.insert (bid block) nblock) cfg
        where
        mapQuad f1 f2 x = case x of
            QAss v1 v2 -> QAss (f1 v1) (f2 v2)
            QOp v1 v2 op v3 -> QOp (f1 v1) (f2 v2) op (f2 v3)
            QNeg v1 v2 -> QNeg (f1 v1) (f2 v2)
            QNot v1 v2 -> QNot (f1 v1) (f2 v2)
            QIf v1 op v2 label -> QIf (f2 v1) op (f2 v2) label
            QJmp _ -> x
            QLabel _ -> x
            QCall v1 ident vals -> QCall (f1 v1) ident (map f2 vals)
            QCallV ident vals -> QCallV ident (map f2 vals)
            QRet v1 -> QRet (f2 v1)
            QRetV -> x
        mapVal f val = case val of
            Var v -> Var $ f v
            VStrRef v -> VStrRef $ f v
            _ -> val
        newVar = Variable <$> (modify (liftNextVar (+1)) >> gets next_var)
        mapNewVar v = do
            nv <- newVar
            modify (liftVarMap (Map.insert v nv))
            modify (liftRevMap (Map.insert nv v))
            return nv
        foldQuads (acc, cused, cdef) q = do
            vmap <- gets var_map
            let dv = getDefinedVariables q
            ndv <- mapM mapNewVar dv
            let nused = Set.union (Set.fromList (map (vmap Map.!) (getUsedVariables q))) cused
            let ndef = Set.union (Set.fromList ndv) cdef
            let nq = mapQuad (mapVal (\_ -> head ndv)) (mapVal (\v -> vmap Map.! v)) q : acc
            return (nq, nused, ndef)
    elimPhi :: SSAState -> FlowGraph -> FlowGraph
    --elimPhi _ cfg | pTrace ("elimPhi: FlowGraph:\n" ++ show cfg) False = undefined
    elimPhi fstate cfg =
        foldl foldBlocks cfg (graph_nodes cfg)
        where
        foldBlocks :: FlowGraph -> SimpleBlock -> FlowGraph
        foldBlocks graph node =
            let (movs, npostal) =
                    foldl foldNgbs ([],[]) ((out_edges graph) IntMap.! (bid node)) in
            let (lq:rq) = reverse $ code node in
            let ncode = case lq of
                    QIf _ _ _ _ -> (lq:(movs ++ rq))
                    QJmp _ -> (lq:(movs ++ rq))
                    QRet _ -> (lq:(movs ++ rq))
                    QRetV -> (lq:(movs ++ rq))
                    _ -> movs ++ (lq:rq) in
            liftNodes (IntMap.insert (bid node)
                    (liftCode (\_ -> reverse ncode)
                    (liftPostAlive (\_ -> Set.fromList npostal) node))) graph
            where
            foldNgbs (cmds, npostal) ngbid =
                let ngb = (graph_nodes cfg) IntMap.! ngbid in
                let postal = sort $ map (\var -> ((rev_map fstate) Map.! var, var))
                        (Set.toList (post_alive node)) in
                let preal = sort $ map (\var -> ((rev_map fstate) Map.! var, var))
                        (Set.toList (pre_alive ngb)) in
                let common = mergeVars preal postal [] in
                let ncmds = map (\(v1, v2) -> QAss (Var v1) (Var v2)) common ++ cmds in
                let npostal2 = map fst common ++ npostal in
                (ncmds, npostal2)
                where
                mergeVars [] _ a = a
                mergeVars _ [] a = a
                mergeVars l1@((v1,r1):v1s) l2@((v2,r2):v2s) a =
                    if v1 < v2 then mergeVars v1s l2 a
                    else if v1 > v2 then mergeVars l1 v2s a
                    else mergeVars v1s v2s ((r1,r2):a)

type Graph = Map.Map Variable [Variable]
type ListGraph = [(Variable, [Variable])]
type Coloring = Map.Map Variable Int

getDefinedVariables :: Quadruple -> [Variable]
getDefinedVariables q = case q of
    QAss (Var v) _ -> [v]
    QAss (VStrRef v) _ -> [v]
    QOp (Var v) _ _ _ -> [v]
    QOp (VStrRef v) _ _ _ -> [v]
    QNeg (Var v) _ -> [v]
    QNot (Var v) _ -> [v]
    QCall (Var v) _ _ -> [v]
    QCall (VStrRef v) _ _ -> [v]
    _ -> []

getUsedVariables :: Quadruple -> [Variable]
getUsedVariables q = case q of
    QAss _ (Var v) -> [v]
    QAss _ (VStrRef v) -> [v]
    QOp _ v1 _ v2 ->
        let r1 = case v1 of
                Var v -> [v]
                VStrRef v -> [v]
                _ -> [] in
        case v2 of
                Var v -> v:r1
                VStrRef v -> v:r1
                _ -> r1
    QNeg _ (Var v) -> [v]
    QNot _ (Var v) -> [v]
    QIf v1 _ v2 _ ->
        let r1 = case v1 of
                Var v -> [v]
                VStrRef v -> [v]
                _ -> [] in
        case v2 of
                Var v -> v:r1
                VStrRef v -> v:r1
                _ -> r1
    QCall _ _ args -> foldl (\acc arg -> case arg of
            Var v -> v:acc
            VStrRef v -> v:acc
            _ -> acc) [] args
    QCallV _ args -> foldl (\acc arg -> case arg of
            Var v -> v:acc
            VStrRef v -> v:acc
            _ -> acc) [] args
    QRet (Var v) -> [v]
    QRet (VStrRef v) -> [v]
    _ -> []

getAllVariables :: Quadruple -> [Variable]
getAllVariables q = (getDefinedVariables q) ++ (getUsedVariables q)


--removeDups :: Ord a => [a] -> [a]
--removeDups l = snd $ foldl f (Set.empty, []) l where
--    f (s, a) v = if Set.member v s then (s, a) else (Set.insert v s, v:a)

collisionGraph :: FlowGraph -> ListGraph
collisionGraph cfg | pTrace ("FlowGraph: " ++ show cfg) False = undefined
collisionGraph cfg =
    let mgraph = foldl genGraph Map.empty (graph_nodes cfg) in
    map (\(v, s) -> (v, Set.toList s)) (Map.assocs mgraph)
    where
    genGraph acc node =
        fst $ foldr iterQuads (acc, post_alive node) (code node)
    iterQuads quad (graph, alive) =
        let graph0 = foldl (\acc v -> Map.insertWith (Set.union) v (Set.empty) acc)
                graph (getAllVariables quad) in
        let nalive = Set.union (alive Set.\\ (Set.fromList (getDefinedVariables quad)))
                (Set.fromList (getUsedVariables quad)) in
        let graph1 = foldl (\acc v -> foldl (\a newe ->
                Map.insertWith (Set.union) v (Set.singleton newe) a) acc (Set.delete v nalive))
                graph0 nalive in
        (graph1, nalive)

graphColoring :: ListGraph -> (Coloring, Int)
graphColoring g | pTrace ("graph: " ++ show g) False = undefined
graphColoring g =
    orderedGraphColoring (orderGraph (Set.fromList $ map (\(a,b) -> (0 :: Integer, a, b)) g) [])
    where
    orderGraph set acc = case Set.lookupMax set of
        Just (_, v, edges) ->
            let nset = Set.map (\(nw, nv, ne) ->
                    if elem nv edges then (nw + 1, nv, ne) else (nw, nv, ne))
                    (Set.deleteMax set) in
            orderGraph nset ((v, edges):acc)
        Nothing -> reverse acc



orderedGraphColoring :: ListGraph -> (Coloring, Int)
orderedGraphColoring g = foldl foldGraph (Map.empty, 0) g where
    foldGraph (coloring, nc) (v, l) =
        (Map.insert v color coloring, if color < nc then nc else nc + 1) where
        color = mexSorted 0 (sort (map (coloring Map.!) (filter (`Map.member` coloring) l))) where
            mexSorted n (x:xs) = if x == n then mexSorted (n+1) xs else n
            mexSorted n [] = n
