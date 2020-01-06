{-# LANGUAGE CPP #-} --for ifdef
module Compiler where

import qualified Data.Map.Strict as Map
import Data.DList(DList, singleton, toList, fromList)
import qualified Data.DList as DList(map, concat, append, empty)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Quadruples
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

data Register = RAX | RBX | RCX | RDX | RSI | RDI | R8 | R9 | R10 | R11 | R12 |R13 | R14 | R15
        | RSP | RBP
    deriving (Eq, Ord)

saved_registers :: [Register]
saved_registers = [RBX, RCX, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15, RDX]

arch_registers :: [Register]
arch_registers = [RBX, R8, R9, R10, R11, R12, R13, R14, R15, RSI, RDI, RCX, RDX, RAX]

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
    deriving (Eq, Show)

data Argument = Loc Location | StrRef Int | Const Integer
    deriving Eq

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
    | ISetl Register
    | ISetle Register
    | ISetg Register
    | ISetge Register
    | ISete Register
    | ISetne Register
    | INeg Location
    | ICQO
    | IStrCmp
    | IXchg Argument Argument

parseLocation :: Int -> Location -> String
parseLocation arg_off loc = case loc of
    Reg r -> show r
    LocVar n -> show (-n*8) ++ "(%rbp)"
    ArgVar n -> show (arg_off + n * 8) ++ "(%rbp)"

parseArgument :: Int -> Argument -> String
parseArgument arg_off arg = case arg of
    Loc loc -> parseLocation arg_off loc
    StrRef n -> "$_s" ++ show n
    Const n -> "$" ++ show n

parseInstr :: Int -> Instruction -> String
parseInstr ao instr = case instr of
    IMov arg loc -> "movq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IAdd arg loc -> "addq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    ISub arg loc -> "subq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IMul arg loc -> "imulq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IDiv arg -> "idivq " ++ parseArgument ao arg
    IPush arg -> "pushq " ++ parseArgument ao arg
    IPop loc -> "popq " ++ parseLocation ao loc
    ICmp arg1 arg2 -> "cmpq " ++ parseArgument ao arg2 ++ ", " ++ parseArgument ao arg1
    IJmpS str -> "jmp " ++ str
    IJmp label -> "jmp " ++ show label
    IJe label -> "je " ++ show label
    IJne label -> "jne " ++ show label
    IJlt label -> "jl " ++ show label
    IJle label -> "jle " ++ show label
    IJgt label -> "jg " ++ show label
    IJge label -> "jge " ++ show label
    ILabel label -> show label ++ ":"
    IAnd arg loc -> "andq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IOr arg loc -> "orq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    IXor arg loc -> "xorq " ++ parseArgument ao arg ++ ", " ++ parseLocation ao loc
    INot loc -> "notq " ++ parseLocation ao loc
    ICall str -> "call " ++ str
    ISetl reg -> "setl " ++ showRegB reg ++ "\n" ++ "andq $1, " ++ show reg
    ISetle reg -> "setle " ++ showRegB reg ++ "\n" ++ "andq $1, " ++ show reg
    ISetg reg -> "setg " ++ showRegB reg ++ "\n" ++ "andq $1, " ++ show reg
    ISetge reg -> "setge " ++ showRegB reg ++ "\n" ++ "andq $1, " ++ show reg
    ISete reg -> "sete " ++ showRegB reg ++ "\n" ++ "andq $1, " ++ show reg
    ISetne reg -> "setne " ++ showRegB reg ++ "\n" ++ "andq $1, " ++ show reg
    INeg loc -> "negq " ++ parseLocation ao loc
    ICQO -> "cqo"
    IXchg arg1 arg2 -> "xchgq " ++ parseArgument ao arg1 ++ ", " ++ parseArgument ao arg2
    IStrCmp -> unlines ["movl (%rdi), %ecx",
                        "addq $4, %rdi",
                        "addq $4, %rsi",
                        "cld",
                        "repe cmpsb"]

type Color = Int
type LEnv = Map.Map Color Location
data CState = CState {lenv :: LEnv
    , var_regs :: Map.Map Variable Register
    , strings :: [String]
    , n_strings :: Int
    , labels :: Int
    , locations :: [Location]
    , register_colors :: Map.Map Register Color}
    deriving Show
data CEnv = CEnv {coloring :: Coloring, end_label :: String}
type Result w a = ReaderT CEnv (WriterT (DList w) (State CState)) a

liftLEnv :: (LEnv -> LEnv) -> CState -> CState
liftLEnv f s = s{lenv = f (lenv s)}

liftVarRegs :: (Map.Map Variable Register -> Map.Map Variable Register) -> CState -> CState
liftVarRegs f s = s{var_regs = f (var_regs s)}

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

locationToRegister :: Location -> Register
locationToRegister (Reg r) = r
locationToRegister _ = error "not a register"

allocString :: String -> Result w Int
allocString str = do
    modify $ (liftStrings (str:)) . (liftNStrings (+1))
    gets n_strings

isRegister :: Location -> Bool
isRegister (Reg _) = True
isRegister _ = False

isRegisterArg :: Argument -> Bool
isRegisterArg (Loc (Reg _)) = True
isRegisterArg _ = False

usedRegisters :: [Location] -> [Register]
usedRegisters locs = filter (\reg -> not $ elem (Reg reg) locs) saved_registers

escapeChar :: Char -> String
escapeChar c = case c of
    '\\' -> "\\\\"
    '\"' -> "\\\""
    _ -> [c]

escapeString :: String -> String
escapeString str = foldr (\c acc-> (escapeChar c) ++ acc) "" str

stringDef :: Int -> String -> String
stringDef n str = "_s" ++ show n ++ ": .long " ++ show (length str) ++
    "\n.ascii \"" ++ (escapeString str) ++ "\""

compileProgram :: TEnv -> Program -> String
compileProgram types (Program topdefs) =
    let (instrs, fin_state) = runState
            (foldM (\acc td ->
                (DList.append acc) <$> (compileTopDef types td)) DList.empty topdefs)
            (CState {lenv = Map.empty
                , var_regs = Map.empty
                , strings = []
                , n_strings = 0
                , labels = 0
                , locations = []
                , register_colors = Map.empty}) in
    let str_defs = fst (foldr (\str (acc, n) -> (stringDef n str : acc, n + 1))
                  ([], 1 :: Int) (strings fin_state)) in
    unlines $ [".text"] ++
        str_defs ++
        [".global _start",
        "_start:",
        "call main",
        "movq %rax, %rdi",
        "movl $60, %eax",
        "syscall"] ++
        toList instrs

compileTopDef :: TEnv -> TopDef -> State CState (DList String)
compileTopDef _ (FnDef _ x _ _) | trace ("compileTopDef: " ++ show x) False = undefined
compileTopDef types x@(FnDef _ (Ident fname) args _) = do
    let endl = "_end_" ++ fname
    nxt_label <- gets labels
    let (quadruples, color, ncolors) = convertTopDef nxt_label types x

    if (pTrace ("Coloring:\n" ++ show color) False) then error "apud" else return ()

    let nargs = length args
    modify $ liftLEnv (\_ -> Map.empty)
    mapM_ (\n -> modify (liftLEnv (Map.insert (color Map.! (Variable n)) (ArgVar n))))
        [0 .. nargs - 1]

    --debug_lenv <- gets lenv
    --if pTrace ("LEnv:\n" ++ show debug_lenv) False then error "" else return ()

    modify $ liftLocations (\_ -> (map Reg arch_registers) ++ (map LocVar [1..ncolors]))
    modify $ liftRegisterColors (\_ -> Map.empty)
    modify $ liftVarRegs (\_ -> Map.empty)
    func_body <- execWriterT $ runReaderT (compileQuadruples quadruples) (CEnv color endl)
    used_regs <- (map show) <$> usedRegisters <$> gets locations

    deb_state <- get
    if pTrace ("Finished compile: " ++ fname ++
            "\nFinal state: " ++ show deb_state)
            False then error "" else return ()

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
    compileQuadruple x | trace ("compileQuadruple " ++ show x) False = undefined
    compileQuadruple x = case x of
        QAss (Var var) val -> do
            tcol <- getColor var
            tloc <- assignLocation var tcol
            case val of
                Var v -> do
                    scol <- getColor v
                    if scol == tcol then return ()
                    else do
                        sloc <- getLocationErr v scol
                        tell $ singleton $ IMov (Loc (Reg sloc)) (Reg tloc)
                VInt int -> tell $ singleton $ IMov (Const int) (Reg tloc)
                VBool b -> tell $ singleton $ IMov (Const (if b then 1 else 0)) (Reg tloc)
                VString s -> do
                    n <- allocString s
                    tell $ singleton $ IMov (StrRef n) (Reg tloc)
                VStrRef v -> compileQuadruple (QAss (Var var) (Var v))
        QAss (VStrRef v) val -> compileQuadruple (QAss (Var v) val)
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
                        Just col2 | (col2 == tcol || mcol1 == Nothing) -> case operation of
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
                (arg, tloc) <- getOperands val
                case op of
                    OAdd -> tell $ singleton $ IAdd arg (Reg tloc)
                    OSub -> tell $ singleton $ ISub arg (Reg tloc)
                    OMul -> tell $ singleton $ IMul arg (Reg tloc)
                    OLTH -> tell $ fromList [ICmp (Loc (Reg tloc)) arg , ISetl tloc]
                    OLE  -> tell $ fromList [ICmp (Loc (Reg tloc)) arg , ISetle tloc]
                    OGTH -> tell $ fromList [ICmp (Loc (Reg tloc)) arg , ISetg tloc]
                    OGE  -> tell $ fromList [ICmp (Loc (Reg tloc)) arg , ISetge tloc]
                    OEQU -> do
                        case val of
                            VString _ -> compareStrings (Loc (Reg tloc)) arg
                            VStrRef _ -> compareStrings (Loc (Reg tloc)) arg
                            _ -> tell $ singleton $ ICmp (Loc (Reg tloc)) arg
                        tell $ singleton $ ISete tloc
                    ONE  -> do
                        case val of
                            VString _ -> compareStrings (Loc (Reg tloc)) arg
                            VStrRef _ -> compareStrings (Loc (Reg tloc)) arg
                            _ -> tell $ singleton $ ICmp (Loc (Reg tloc)) arg
                        tell $ singleton $ ISetne tloc
                    _ -> error $ "operation " ++ show op ++ " not allowed here"
                where
                getOperands v = do
                    tcol <- getColor var
                    tloc <- assignLocation var tcol
                    case v of
                        Var var2 -> do
                            scol <- getColor var2
                            sloc <- getLocationErr var2 scol
                            return (Loc (Reg sloc), tloc)
                        VInt int | op == OMul -> return (Const int, tloc)
                        VInt int -> return (Const int, tloc)
                        VBool b -> return (Const (if b then 1 else 0), tloc)
                        VString str -> do
                            n <- allocString str
                            return (StrRef n, tloc)
                        VStrRef var2 -> getOperands (Var var2)
            compileDiv var val1 op val2 = do
                tloc <- getColor var >>= assignLocation var
                locs <- gets locations
                if not (elem (Reg RDX) locs) && (tloc /= RDX || op == ODiv) then
                    tell $ singleton $ IPush (Loc (Reg RDX))
                else return ()
                if not (elem (Reg RAX) locs) && (tloc /= RAX || op == OMod) then
                    tell $ singleton $ IPush (Loc (Reg RAX))
                else return ()
                case val1 of
                    Var v -> do
                        scol <- getColor v
                        sloc <- getLocationErr v scol
                        if sloc /= RAX then
                            tell $ singleton $ IMov (Loc (Reg sloc)) (Reg RAX)
                        else return ()
                    VInt int -> tell $ singleton $ IMov (Const int) (Reg RAX)
                    _ -> error "not supported div operand"
                tell $ singleton $ ICQO
                case val2 of
                    Var v -> do
                        scol <- getColor v
                        sloc <- getLocationErr v scol
                        tell $ singleton $ IDiv (Loc (Reg sloc))
                    VInt int -> do
                        loc <- head <$> (gets locations)
                        tell $ fromList [IMov (Const int) loc,
                                        IDiv (Loc loc)]
                    _ -> error "not a div operand"
                case op of
                    ODiv | tloc == RAX -> return ()
                    ODiv -> tell $ singleton $ IMov (Loc (Reg RAX)) (Reg tloc)
                    OMod | tloc == RDX -> return ()
                    OMod -> tell $ singleton $ IMov (Loc (Reg RDX)) (Reg tloc)
                    _ -> error "not a div operator"
                if not (elem (Reg RAX) locs) && (tloc /= RAX || op == OMod) then
                    tell $ singleton $ IPop (Reg RAX)
                else return ()
                if not (elem (Reg RDX) locs) && (tloc /= RDX || op == ODiv) then
                    tell $ singleton $ IPop (Reg RDX)
                else return ()
            compileConcat var val1 val2 =
                compileQuadruple (QCall (Var var) (Ident "_concat") [val1, val2])
        QOp (VStrRef res) arg1 op arg2 -> compileQuadruple (QOp (Var res) arg1 op arg2)
        QNeg (Var var) val -> do
            tloc <- getColor var >>= assignLocation var
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr v
                    if sloc /= tloc then
                        tell $ singleton $ IMov (Loc (Reg sloc)) (Reg tloc)
                    else return ()
                    tell $ singleton $ INeg (Reg tloc)
                VInt int -> tell $ singleton $ IMov (Const (-int)) (Reg tloc)
                _ -> error $ "cannot negate " ++ show val
        QNot (Var var) val -> do
            tloc <- getColor var >>= assignLocation var
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr v
                    if sloc /= tloc then
                        tell $ singleton $ IMov (Loc (Reg sloc)) (Reg tloc)
                    else return ()
                    tell $ singleton $ INot (Reg tloc)
                VBool b -> tell $ singleton $ IMov (Const (if b then 0 else 1)) (Reg tloc)
                _ -> error $ "cannot not " ++ show val
        QIf val1 op val2 label -> do
            c1 <- getMaybeColor val1
            case c1 of
                Nothing -> compileQuadruple (QIf val2 (case op of
                        OLTH -> OGTH
                        OLE -> OGE
                        OGTH -> OLTH
                        OGE -> OLE
                        _ -> op) val1 label)
                Just _ -> do
                    arg1 <- valToArg val1
                    arg2 <- valToArg val2
                    case op of
                        OLTH -> tell $ fromList [ICmp arg1 arg2, IJlt label]
                        OLE -> tell $ fromList [ICmp arg1 arg2, IJle label]
                        OGTH -> tell $ fromList [ICmp arg1 arg2, IJgt label]
                        OGE -> tell $ fromList [ICmp arg1 arg2, IJge label]
                        OEQU -> do
                            case val1 of
                                VString _ -> compareStrings arg1 arg2
                                VStrRef _ -> compareStrings arg1 arg2
                                _ -> tell $ singleton $ ICmp arg1 arg2
                            tell $ singleton $ IJe label
                        ONE -> do
                            case val1 of
                                VString _ -> compareStrings arg1 arg2
                                VStrRef _ -> compareStrings arg1 arg2
                                _ -> tell $ singleton $ ICmp arg1 arg2
                            tell $ singleton $ IJne label
                        _ -> error $ "not an if operation: " ++ show op
        QJmp label -> tell $ singleton $ IJmp label
        QLabel label@(Label l) -> do
            modify (liftLabels (max l))
            tell $ singleton $ ILabel label
        QCall (Var var) (Ident fun) args -> do
            locs <- gets locations
            tloc <- getColor var >>= assignLocation var
            if not (elem (Reg RAX) locs) && tloc /= RAX then
                tell $ singleton $ IPush (Loc (Reg RAX))
            else return ()
            mapM_ compilePush (reverse args)
            tell $ singleton $ ICall fun
            if tloc /= RAX then
                tell $ singleton $ IMov (Loc (Reg RAX)) (Reg tloc)
            else return ()
            if args /= [] then
                tell $ singleton $ IAdd (Const (8 * (toInteger $ length args))) (Reg RSP)
            else return ()
            if not (elem (Reg RAX) locs) && tloc /= RAX then
                tell $ singleton $ IPop (Reg RAX)
            else return ()
        QCall (VStrRef var) fun args -> compileQuadruple (QCall (Var var) fun args)
        QCallV (Ident fun) args -> do
            mapM_ compilePush (reverse args)
            tell $ singleton $ ICall fun
            if args /= [] then
                tell $ singleton $ IAdd (Const (8 * (toInteger $ length args))) (Reg RSP)
            else return ()
        QRet val -> do
            case val of
                Var v -> do
                    loc <- getColor v >>= getLocationErr v
                    tell $ singleton $ IMov (Loc (Reg loc)) (Reg RAX)
                VInt int -> tell $ singleton $ IMov (Const int) (Reg RAX)
                VBool b -> tell $ singleton $ IMov (Const (if b then 1 else 0)) (Reg RAX)
                VString str -> do
                    n <- allocString str
                    tell $ singleton $ IMov (StrRef n) (Reg RAX)
                VStrRef v -> compileQuadruple (QRet (Var v))
            endl <- asks end_label
            tell $ singleton $ IJmpS endl
        QRetV -> do
            endl <- asks end_label
            tell $ singleton $ IJmpS endl
        _ -> error "wrong quadruple"
        where
        assignLocation :: Variable -> Color -> Result Instruction Register
        assignLocation var c = do
            curloc <- getLocation c
            nloc <- case curloc of
                Just loc -> do
                    return loc
                Nothing -> do
                    locs <- gets locations
                    case locs of
                        [] -> error "No free location"
                        (l:ls) -> do
                            modify $ (liftLocations (\_ -> ls)) . (liftLEnv (Map.insert c l))
                            case l of
                                Reg reg -> modify $ liftRegisterColors (Map.insert reg c)
                                _ -> return ()
                            return l
            reg <- case nloc of
                Reg r -> return r
                _ -> swapToRegister quads c
            vregs <- gets var_regs
            case vregs Map.!? var of
                Just vreg | vreg /= reg -> do
                    tell $ singleton $ IXchg (Loc (Reg vreg)) (Loc (Reg reg))
                    vregc <- gets $ (Map.! vreg).register_colors
                    modify $ liftLEnv (Map.insert vregc (Reg reg))
                    modify $ liftLEnv (Map.insert c (Reg vreg))
                    modify $ liftRegisterColors (Map.insert vreg c)
                    modify $ liftRegisterColors (Map.insert reg vregc)
                    return vreg
                Nothing -> do
                    modify $ liftVarRegs (Map.insert var reg)
                    return reg
                Just _ -> return reg

        getLocationErr :: Variable -> Color -> Result Instruction Register
        getLocationErr var c = do
            mloc <- getLocation c
            vregs <- gets var_regs
            case mloc of
                Just (Reg r) -> return r
                Just _ -> do
                    reg <- swapToRegister quads c
                    if not (Map.member var vregs) then
                        modify $ liftVarRegs (Map.insert var reg)
                    else return ()
                    return reg
                Nothing -> do
                    if not (Map.member var vregs) then
                        assignLocation var c
                    else do
                        debug_lenv <- gets lenv
                        debug_c <- asks coloring
                        error $ "No location for var: " ++ show var ++ " color: " ++ show c
                                ++ "\n LEnv: " ++ show debug_lenv
                                ++ "\n quads:\n" ++ (unlines (map show (quad:quads)))
                                ++ "\n var_regs:\n" ++ (unlines (map show (Map.toList vregs)))
                                ++ "\n colloring:\n" ++ (unlines (map show (Map.toList debug_c)))

        valToArg :: Val -> Result Instruction Argument
        valToArg val = case val of
            Var var -> Loc <$> Reg <$> (getColor var >>= getLocationErr var)
            VInt int -> return $ Const int
            VBool b -> return $ Const $ if b then 1 else 0
            VString str -> do
                n <- allocString str
                return $ StrRef n
            VStrRef v -> valToArg (Var v)

        compilePush :: Val -> Result Instruction ()
        compilePush val = do
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr v
                    tell $ singleton $ IPush (Loc (Reg sloc))
                VInt int -> tell $ singleton $ IPush (Const int)
                VBool b -> tell $ singleton $ IPush (Const (if b then 1 else 0))
                VStrRef v -> compilePush (Var v)
                VString str -> do
                    n <- allocString str
                    tell $ singleton $ IPush (StrRef n)


compareStrings :: Argument -> Argument -> Result Instruction ()
compareStrings arg1 arg2 = do
    locs <- gets locations
    backupRegister locs RDI
    backupRegister locs RSI
    backupRegister locs RCX
    if arg1 /= (Loc (Reg RDI)) then
        tell $ singleton $ IMov arg1 (Reg RDI)
    else return ()
    if arg2 /= (Loc (Reg RSI)) then
        tell $ singleton $ IMov arg2 (Reg RSI)
    else return ()
    tell $ singleton $ IStrCmp
    restoreRegister locs RCX
    restoreRegister locs RSI
    restoreRegister locs RDI
    where
    backupRegister :: [Location] -> Register -> Result Instruction ()
    backupRegister locs reg = do
        if not (elem (Reg reg) locs) then
            tell $ singleton $ IPush (Loc (Reg reg))
        else return ()

    restoreRegister :: [Location] -> Register -> Result Instruction ()
    restoreRegister locs reg = do
        if not (elem (Reg reg) locs) then
            tell $ singleton $ IPop (Reg reg)
        else return ()

swapToRegister :: [Quadruple] -> Color -> Result Instruction Register
swapToRegister quads c = do
    cmap <- asks coloring
    msloc <- getLocation c
    let sloc = case msloc of
            Just loc -> loc
            Nothing -> error $ "swapToRegister: no location for color: " ++ show c
    locs <- gets locations
    case locs of
        [] -> error "No free location"
        (l@(Reg treg):ls) -> do
            modify $ (liftLocations (\_ -> ls)) .
                    (liftLEnv (Map.insert c l)) .
                    (liftRegisterColors (Map.insert treg c))
            tell (singleton (IMov (Loc sloc) l))
            return treg
        _ -> do
            (_, regc, treg) <- gets $ maximum .
                (map (\(reg,col) ->
                    (nextUse cmap col quads, col, reg))) . Map.assocs . register_colors
            let tloc = Reg treg
            tell $ singleton $ IXchg (Loc sloc) (Loc tloc)
            modify $ (liftLEnv (Map.insert c tloc)) .
                    (liftLEnv (Map.insert regc sloc)) .
                    (liftRegisterColors (Map.insert treg c))
            return treg

nextUse :: Coloring -> Color -> [Quadruple] -> Int
nextUse cmap col q = nextUseAcum cmap col q 1

nextUseAcum :: Coloring -> Color -> [Quadruple] -> Int -> Int
nextUseAcum _ _ [] _ = maxBound
nextUseAcum cmap col (x:xs) a =
    if elem col (map (cmap Map.!) (getAllVariables x)) then a
    else nextUseAcum cmap col xs (a+1)

