module Compiler where

import qualified Data.Map.Strict as Map
import Data.DList(DList, singleton, toList, fromList)
import qualified Data.DList as DList(map, concat, append, empty)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Quadruples
import AbsLatte

data Register = RAX | RBX | RCX | RDX | RSI | RDI | R8 | R9 | R10 | R11 | R12 |R13 | R14 | R15
        | RSP | RBP
    deriving (Eq, Ord)

saved_registers :: [Register]
saved_registers = [RBX, RCX, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15, RDX]

arch_registers :: [Register]
arch_registers = [RBX, RCX, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15, RDX, RAX]

n_arch_registers :: Int
n_arch_registers = 14

instance Show Register where
    show reg = case reg of
        RBX -> "%rbx"
        RCX -> "%rcx"
        RSI -> "%rsi"
        RDI -> "%rdi"
        R8 -> "%r8"
        R9 -> "%r9"
        R10 -> "%r10"
        R11 -> "%r11"
        R12 -> "%r12"
        R13 -> "%r13"
        R14 -> "%r14"
        R15 -> "%r15"
        RDX -> "%rdx"
        RAX -> "%rax"
        RSP -> "%rsp"
        RBP -> "%rbp"

showRegB:: Register -> String
showRegB reg = case reg of
    RBX -> "%bl"
    RCX -> "%cl"
    RSI -> "%sil"
    RDI -> "%dil"
    R8  -> "%r8b"
    R9  -> "%r9b"
    R10 -> "%r10b"
    R11 -> "%r11b"
    R12 -> "%r12b"
    R13 -> "%r13b"
    R14 -> "%r14b"
    R15 -> "%r15b"
    RDX -> "%dl"
    RAX -> "%al"
    RSP -> "%spl"
    RBP -> "%bpl"

data Location = Reg Register | LocVar Int | ArgVar Int
    deriving Eq

data Argument = Loc Location | StrRef Int | Const Integer

data Instruction
    = IMov Argument Location
    | IAdd Argument Location
    | ISub Argument Location
    | IMul Argument Location
    | IDiv Argument
    | IPush Argument
    | IPop Location
    | ICmp Argument Argument
    | IJmpS String
    | IJmp Label
    | IJe Label
    | IJne Label
    | IJlt Label
    | IJle Label
    | IJgt Label
    | IJge Label
    | ILabel Label
    | IAnd Argument Location
    | IOr Argument Location
    | IXor Argument Location
    | INot Location
    | ICall String
    | ISetl Location
    | ISetle Location
    | ISetg Location
    | ISetge Location
    | ISete Location
    | ISetne Location

parseLocation :: Int -> Location -> String
parseLocation arg_off loc = case loc of
    Reg r -> show r
    LocVar n -> show (-n*8) ++ "(%rbp)"
    ArgVar n -> show (arg_off + n * 8) ++ "(%rbp)"

parseArgument :: Int -> Argument -> String
parseArgument arg_off arg = case arg of
    Loc loc -> parseLocation arg_off loc
    StrRef n -> "_s" ++ show n
    Const n -> "$" ++ show n

parseInstr :: Int -> Instruction -> String
parseInstr ao instr = case instr of
    IMov arg loc -> "movq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IAdd arg loc -> "addq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    ISub arg loc -> "subq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IMul arg loc -> "subq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IDiv arg -> "idivq " ++ parseArgument ao arg
    IPush arg -> "pushq " ++ parseArgument ao arg
    IPop loc -> "popq " ++ parseLocation ao loc
    ICmp arg1 arg2 -> "cmpq " ++ parseArgument ao arg1 ++ ", " ++ parseArgument ao arg2
    IJmpS str -> "jmp " ++ str
    IJmp label -> "jmp " ++ show label
    IJe label -> "je " ++ show label
    IJne label -> "jne " ++ show label
    IJlt label -> "jlt " ++ show label
    IJle label -> "jle " ++ show label
    IJgt label -> "jgt " ++ show label
    IJge label -> "jge " ++ show label
    ILabel label -> show label ++ ":"
    IAnd arg loc -> "andq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IOr arg loc -> "orq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IXor arg loc -> "xorq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    INot loc -> "notq " ++ parseLocation ao loc
    ICall str -> "call " ++ str
    ISetl loc -> "setl " ++ parseLocation ao loc
    ISetle loc -> "setle " ++ parseLocation ao loc
    ISetg loc -> "letg " ++ parseLocation ao loc
    ISetge loc -> "setge " ++ parseLocation ao loc
    ISete loc -> "sete " ++ parseLocation ao loc
    ISetne loc -> "setne " ++ parseLocation ao loc


type Color = Int
type LEnv = Map.Map Color Location
data CState = CState {lenv :: LEnv
    , strings :: [String]
    , n_strings :: Int
    , labels :: Int
    , locations :: [Location]
    , register_colors :: Map.Map Register Color}
data CEnv = CEnv {coloring :: Coloring, end_label :: String}
type Result w a = ReaderT CEnv (WriterT (DList w) (State CState)) a

liftLEnv :: (LEnv -> LEnv) -> CState -> CState
liftLEnv f s = s{lenv = f (lenv s)}

liftStrings :: ([String] -> [String]) -> CState -> CState
liftStrings f s = s{strings = f (strings s)}

liftNStrings :: (Int -> Int) -> CState -> CState
liftNStrings f s = s{n_strings = f (n_strings s)}

liftLabels :: (Int -> Int) -> CState -> CState
liftLabels f s = s{labels = f (labels s)}

liftLocations :: ([Location] -> [Location]) -> CState -> CState
liftLocations f s = s{locations = f (locations s)}

liftRegisterColors :: (Map.Map Register Color -> Map.Map Register Color) -> CState -> CState
liftRegisterColors f s = s{register_colors = f (register_colors s)}

liftColoring :: (Coloring -> Coloring) -> CEnv -> CEnv
liftColoring f s = s{coloring = f (coloring s)}

getColor :: Variable -> Result w Color
getColor v = (Map.! v) <$> asks coloring

getMaybeColor :: Val -> Result w (Maybe Color)
getMaybeColor v = case v of
    Var var -> Just <$> getColor var
    _ -> return Nothing

getLocation :: Color -> Result w (Maybe Location)
getLocation c = (Map.!? c) <$> gets lenv

getLocationErr :: Color -> Result w Location
getLocationErr c = do
    l <- (Map.!? c) <$> gets lenv
    case l of
        Just loc -> return loc
        Nothing -> error "no location"

locationToRegister :: Location -> Register
locationToRegister (Reg r) = r
locationToRegister _ = error "not a register"

assignLocation :: Color -> Result w Location
assignLocation c = do
    curloc <- getLocation c
    case curloc of
        Just loc -> return loc
        Nothing -> do
            locs <- gets locations
            case locs of
                [] -> error "No free location"
                (l:ls) -> modify ((liftLocations (\_ -> ls)).(liftLEnv (\e -> Map.insert c l e)))
                    >> return l

isRegister :: Location -> Bool
isRegister (Reg _) = True
isRegister _ = False

usedRegisters :: [Location] -> [Register]
usedRegisters locs = filter (\reg -> not $ elem (Reg reg) locs) saved_registers

compileProgram :: Program -> String
compileProgram (Program topdefs) =
    let (instrs, fin_state) = runState
            (foldM (\acc td -> (DList.append acc) <$> (compileTopDef td)) DList.empty topdefs)
            (CState {lenv = Map.empty
                , strings = []
                , n_strings = 0
                , labels = 0
                , locations = []
                , register_colors = Map.empty}) in
    let str_defs = fst (foldr (\str (acc, n) ->
            (("_s" ++ (show n) ++ ": .ascii \"" ++ str ++"\\0\"") : acc, n + 1))
                  ([], 1 :: Integer) (strings fin_state)) in
    unlines $ [".text"] ++
        str_defs ++
        [".global _main",
        "_main:",
        "call main"] ++
        toList instrs

compileTopDef :: TopDef -> State CState (DList String)
compileTopDef x = case x of
  FnDef _ (Ident fname) args _ -> do
    let endl = "_end_" ++ fname
    nxt_label <- gets labels
    let (quadruples, color) = convertTopDef nxt_label x
    let nargs = length args
    mapM_ (\n -> modify (liftLEnv (Map.insert (color Map.! (Variable n)) (ArgVar n))))
        [0 .. nargs - 1]
    modify (liftLocations (\_ -> (map Reg arch_registers) ++ (map LocVar [1..])))
    func_body <- execWriterT $ runReaderT (compileQuadruples quadruples) (CEnv color endl)
    used_regs <- (map show) <$> usedRegisters <$> gets locations
    return $ DList.concat [fromList (
            [fname ++ ":"] ++
            map ("pushq " ++) used_regs ++
            ["pushq %rbp"
            , "movq %rsp, %rbp"]),
            DList.map (parseInstr (8 * (length used_regs + 2))) func_body,
            fromList (
            [endl ++ ":"
            , "movq %rbp, %rsp"
            , "popq %rbp"] ++
            map ("popq " ++) (reverse used_regs) ++
            ["ret"])]

compileQuadruples :: [Quadruple] -> Result Instruction ()
compileQuadruples [] = return ()
compileQuadruples (quad:quads) = compileQuadruple quad >> compileQuadruples quads where
    compileQuadruple x = case x of
        QAss (Var var) val -> do
            tcol <- getColor var
            loc <- assignLocation tcol
            case val of
                Var v -> do
                    scol <- getColor v
                    if scol == tcol then return ()
                    else do
                        sloc <- getLocationErr scol
                        tloc <- if not (isRegister loc || isRegister sloc) then
                            swapToRegister quads tcol
                        else return loc
                        tell $ singleton $ IMov (Loc sloc) tloc
                VInt int -> tell $ singleton $ IMov (Const int) loc
                VBool b -> tell $ singleton $ IMov (Const (if b then 1 else 0)) loc
                VString s -> do
                    modify $ (liftStrings (s:)) . (liftNStrings (+1))
                    n <- gets n_strings
                    tell $ singleton $ IMov (StrRef n) loc
                VStrRef v -> compileQuadruple (QAss (Var var) (Var v))
        QOp (Var res) arg1 operation arg2 -> do
            if operation == ODiv || operation == OMod then compileDiv res arg1 operation arg2
            else if operation == OConcat then compileConcat res arg1 arg2
            else do
                tcol <- getColor res
                mcol1 <- getMaybeColor arg1
                mcol2 <- getMaybeColor arg2
                case mcol1 of
                    Just col1 | col1 == tcol -> do
                        compileQuadruple (QAss (Var res) arg1)
                        compileOperation res operation arg2
                    _ -> case mcol2 of
                        Just col2 | col2 == tcol -> case operation of
                            OSub -> do
                                compileQuadruple (QNeg (Var res) arg2)
                                compileOperation res OAdd arg1
                            OLTH -> swapOrder OGTH
                            OLE -> swapOrder OGE
                            OGTH -> swapOrder OLTH
                            OGE -> swapOrder OLE
                            _ -> swapOrder operation
                            where
                            swapOrder o = do
                                compileQuadruple (QAss (Var res) arg2)
                                compileOperation res o arg1
                        _ -> do
                            compileQuadruple (QAss (Var res) arg1)
                            compileOperation res operation arg2
            where
            compileOperation var op val = do
                tcol <- getColor var
                tloc <- assignLocation tcol
                (arg, ntloc) <- case val of
                    Var var2 -> do
                        scol <- getColor var2
                        sloc <- getLocationErr scol
                        ntloc <- if not (isRegister tloc) && (not (isRegister sloc) || op == OMul)
                            then swapToRegister quads tcol
                        else return tloc
                        return (Loc sloc, ntloc)
                    VInt int | op == OMul -> return (Const int, tloc)
                    VInt int -> return (Const int, tloc)
                    VBool b -> return (Const (if b then 1 else 0), tloc)
                    VString str -> do
                        modify $ (liftStrings (str:)) . (liftNStrings (+1))
                        n <- gets n_strings
                        return (StrRef n, tloc)
                    VStrRef _ -> error "string operation not allowed here"
                case op of
                    OAdd -> tell $ singleton $ IAdd arg ntloc
                    OSub -> tell $ singleton $ ISub arg ntloc
                    OMul -> tell $ singleton $ IMul arg ntloc
                    OLTH -> tell $ fromList [ICmp (Loc ntloc) arg, ISetl ntloc]
                    OLE  -> tell $ fromList [ICmp (Loc ntloc) arg, ISetle ntloc]
                    OGTH -> tell $ fromList [ICmp (Loc ntloc) arg, ISetg ntloc]
                    OGE  -> tell $ fromList [ICmp (Loc ntloc) arg, ISetge ntloc]
                    OEQU -> tell $ fromList [ICmp (Loc ntloc) arg, ISete ntloc]
                    ONE  -> tell $ fromList [ICmp (Loc ntloc) arg, ISetne ntloc]
                    _ -> error $ "operation " ++ show op ++ " not allowed here"
            compileDiv var val1 op val2 = do
                tloc <- getColor var >>= assignLocation
                locs <- gets locations
                if not (elem (Reg RDX) locs) && (tloc /= Reg RDX || op == ODiv) then
                    tell $ singleton $ IPush (Loc (Reg RDX))
                else return ()
                if not (elem (Reg RAX) locs) && (tloc /= Reg RAX || op == OMod) then
                    tell $ singleton $ IPush (Loc (Reg RAX))
                else return ()
                case val1 of
                    Var v -> do
                        scol <- getColor v
                        sloc <- getLocationErr scol
                        if sloc /= Reg RAX then
                            tell $ singleton $ IMov (Loc sloc) (Reg RAX)
                        else return ()
                    VInt int -> tell $ singleton $ IMov (Const int) (Reg RAX)
                    _ -> error "not supported div operand"
                tell $ fromList [IMov (Const (2^(63::Integer))) (Reg RDX),
                                IAnd (Loc (Reg RAX)) (Reg RDX),
                                IAnd (Const (2^(63::Integer) - 1)) (Reg RAX)]
                case val2 of
                    Var v -> do
                        scol <- getColor v
                        sloc <- getLocationErr scol
                        tell $ singleton $ IDiv (Loc sloc)
                    VInt int -> tell $ singleton $ IDiv (Const int)
                    _ -> error "not a div operand"
                case op of
                    ODiv | tloc == Reg RAX -> return ()
                    ODiv -> tell $ singleton $ IMov (Loc (Reg RAX)) tloc
                    OMod | tloc == Reg RDX -> return ()
                    OMod -> tell $ singleton $ IMov (Loc (Reg RDX)) tloc
                    _ -> error "not a div operator"
                if not (elem (Reg RAX) locs) && (tloc /= Reg RAX || op == OMod) then
                    tell $ singleton $ IPop (Reg RAX)
                else return ()
                if not (elem (Reg RDX) locs) && (tloc /= Reg RDX || op == ODiv) then
                    tell $ singleton $ IPop (Reg RDX)
                else return ()
            compileConcat var val1 val2 =
                compileQuadruple (QCall (Var var) (Ident "_concat") [val1, val2])
        QNeg (Var var) val -> do
            tloc <- getColor var >>= assignLocation
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr
                    if sloc /= tloc then
                        tell $ singleton $ IMov (Loc sloc) tloc
                    else return ()
                    tell $ fromList [INot tloc, IAdd (Const 1) tloc]
                VInt int -> tell $ singleton $ IMov (Const (-int)) tloc
                _ -> error $ "cannot negate " ++ show val
        QNot (Var var) val -> do
            tloc <- getColor var >>= assignLocation
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr
                    if sloc /= tloc then
                        tell $ singleton $ IMov (Loc sloc) tloc
                    else return ()
                    tell $ singleton $ INot tloc
                VBool b -> tell $ singleton $ IMov (Const (if b then 0 else 1)) tloc
                _ -> error $ "cannot not " ++ show val
        QIf val1 op val2 label -> do
            arg1 <- valToArg val1
            arg2 <- valToArg val2
            case op of
                OLTH -> tell $ fromList [ICmp arg1 arg2, IJlt label]
                OLE -> tell $ fromList [ICmp arg1 arg2, IJle label]
                OGTH -> tell $ fromList [ICmp arg1 arg2, IJgt label]
                OGE -> tell $ fromList [ICmp arg1 arg2, IJge label]
                OEQU -> case val1 of
                    VString str -> return () --TODO string compare
                    VStrRef var -> return () --TODO string compare
                    _ -> tell $ fromList [ICmp arg1 arg2, IJe label]
                ONE -> case val1 of
                    VString str -> return () --TODO string compare
                    VStrRef var -> return () --TODO string compare
                    _ -> tell $ fromList [ICmp arg1 arg2, IJne label]
                _ -> error $ "not an if operation: " ++ show op
            where
            valToArg val = case val of
                Var var -> Loc <$> (getColor var >>= getLocationErr)
                VInt int -> return $ Const int
                VBool b -> return $ Const $ if b then 1 else 0
                VString str -> do
                    modify $ (liftStrings (str:)) . (liftNStrings (+1))
                    n <- gets n_strings
                    return $ StrRef n
                VStrRef v -> valToArg (Var v)
        QJmp label -> tell $ singleton $ IJmp label
        QLabel label@(Label l) -> do
            modify (liftLabels (max l))
            tell $ singleton $ ILabel label
        QCall (Var var) (Ident fun) args -> do
            locs <- gets locations
            tcol <- getColor var
            tloc <- assignLocation tcol
            if not (elem (Reg RAX) locs) && tloc /= Reg RAX then
                tell $ singleton $ IPush (Loc (Reg RAX))
            else return ()
            mapM_ compilePush (reverse args)
            tell $ singleton $ ICall fun
            if tloc /= Reg RAX then
                tell $ singleton $ IMov (Loc (Reg RAX)) tloc
            else return ()
            if args /= [] then
                tell $ singleton $ IAdd (Const (8 * (toInteger $ length args))) (Reg RSP)
            else return ()
            if not (elem (Reg RAX) locs) && tloc /= Reg RAX then
                tell $ singleton $ IPop (Reg RAX)
            else return ()
            where
            compilePush val = do
                case val of
                    Var v -> do
                        sloc <- getColor v >>= getLocationErr
                        tell $ singleton $ IPush (Loc sloc)
                    VInt int -> tell $ singleton $ IPush (Const int)
                    VBool b -> tell $ singleton $ IPush (Const (if b then 1 else 0))
                    VStrRef v -> compilePush (Var v)
                    VString str -> do
                        modify $ (liftStrings (str:)) . (liftNStrings (+1))
                        n <- gets n_strings
                        tell $ singleton $ IPush (StrRef n)
        QRet val -> do
            case val of
                Var v -> do
                    loc <- getColor v >>= getLocationErr
                    tell $ singleton $ IMov (Loc loc) (Reg RAX)
                VInt int -> tell $ singleton $ IMov (Const int) (Reg RAX)
                VBool b -> tell $ singleton $ IMov (Const (if b then 1 else 0)) (Reg RAX)
                VString str ->do
                    modify $ (liftStrings (str:)) . (liftNStrings (+1))
                    n <- gets n_strings
                    tell $ singleton $ IMov (StrRef n) (Reg RAX)
                VStrRef v -> compileQuadruple (QRet (Var v))
            endl <- asks end_label
            tell $ singleton $ IJmpS endl
        QRetV -> do
            endl <- asks end_label
            tell $ singleton $ IJmpS endl
        _ -> error "wrong quadruple"

swapToRegister :: [Quadruple] -> Color -> Result Instruction Location
swapToRegister quads c = do
    cmap <- asks coloring
    sloc <- getLocationErr c
    (_, regc, treg) <- gets $ maximum .
        (map (\(reg,col) -> (nextUse cmap col quads, col, reg))) . Map.assocs . register_colors
    let tloc = Reg treg
    tell $ fromList [IXor (Loc sloc) tloc
                    ,IXor (Loc tloc) sloc
                    ,IXor (Loc sloc) tloc]
    modify $ (liftLEnv (Map.insert c tloc)) .
            (liftLEnv (Map.insert regc sloc)) .
            (liftRegisterColors (Map.insert treg c))
    return tloc


nextUse :: Coloring -> Color -> [Quadruple] -> Int
nextUse cmap col q = nextUseAcum cmap col q 1

nextUseAcum :: Coloring -> Color -> [Quadruple] -> Int -> Int
nextUseAcum _ _ [] _ = maxBound
nextUseAcum cmap col (x:xs) a =
    if elem col (map (cmap Map.!) (getAllVariables x)) then a
    else nextUseAcum cmap col xs (a+1)

