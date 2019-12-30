module Compiler where

import qualified Data.Map.Strict as Map
import Data.DList(DList, singleton, toList, fromList)
import Control.Monad.RWS
import Quadruples
import AbsLatte

data Register = RAX | RBX | RCX | RDX | RSI | RDI | R8 | R9 | R10 | R11 | R12 |R13 | R14 | R15
    deriving (Eq, Ord)

saved_registers :: [Register]
saved_registers = [RBX, RCX, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15, RDX]

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

newtype MemOffset = MemOff Int
    deriving (Eq, Ord)

data Location = Reg Register | MemRel MemOffset
    deriving Eq

instance Show Location where
    show loc = case loc of
        Reg r -> show r
        MemRel (MemOff n) -> (show n) ++ "(%rbp)"

showb :: Location -> String
showb loc = case loc of
    Reg RBX -> "%bl"
    Reg RCX -> "%cl"
    Reg RSI -> "%sil"
    Reg RDI -> "%dil"
    Reg R8  -> "%r8b"
    Reg R9  -> "%r9b"
    Reg R10 -> "%r10b"
    Reg R11 -> "%r11b"
    Reg R12 -> "%r12b"
    Reg R13 -> "%r13b"
    Reg R14 -> "%r14b"
    Reg R15 -> "%r15b"
    Reg RDX -> "%dl"
    Reg RAX -> "%al"
    MemRel (MemOff n) -> (show (n + 7)) ++ "(%rbp)"

instance Show Label where
    show (Label l) = "_l" ++ show l

type Color = Int
type LEnv = Map.Map Color Location
data CState = CState {lenv :: LEnv
    , strings :: [String]
    , n_strings :: Int
    , labels :: Int
    , locations :: [Location]
    , register_colors :: Map.Map Register Color}
data CEnv = CEnv {coloring :: Coloring, n_colors :: Int}
type Result a = RWS CEnv (DList String) CState a

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

liftNColors :: (Int -> Int) -> CEnv -> CEnv
liftNColors f s = s{n_colors = f (n_colors s)}

getColor :: Variable -> Result Color
getColor v = (Map.! v) <$> asks coloring

getMaybeColor :: Val -> Result (Maybe Color)
getMaybeColor v = case v of
    Var var -> Just <$> getColor var
    _ -> return Nothing

getLocation :: Color -> Result (Maybe Location)
getLocation c = (Map.!? c) <$> gets lenv

getLocationErr :: Color -> Result Location
getLocationErr c = do
    l <- (Map.!? c) <$> gets lenv
    case l of
        Just loc -> return loc
        Nothing -> error "no location"

locationToRegister :: Location -> Register
locationToRegister (Reg r) = r
locationToRegister _ = error "not a register"

assignLocation :: Color -> Result Location
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

usedRegisters :: [Location] -> [Register]
usedRegisters locs = filter (\reg -> not $ elem (Reg reg) locs) saved_registers

failure :: Show a => a -> Result ()
failure x = return ()

compileProgram :: Program -> Result ()
compileProgram x = case x of
  Program topdefs -> failure x

compileTopDef :: TopDef -> Result ()
compileTopDef x = case x of
  FnDef type_ ident args block -> failure x

compileArg :: Arg -> Result ()
compileArg x = case x of
  Arg type_ ident -> failure x

compileQuadruples :: Int -> [Quadruple] -> Result ()
compileQuadruples _ [] = return ()
compileQuadruples num (quad:quads) = compileQuadruple quad >> compileQuadruples (num+1) quads where
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
                        tloc <- case (loc, sloc) of
                            (MemRel _, MemRel _) -> swapToRegister quads tcol
                            _ -> return loc
                        tell $ singleton $ "movq " ++ show sloc ++ ", " ++ show tloc
                VInt int -> tell $ singleton $ "movq $" ++ show int ++ ", " ++ show loc
                VBool b -> tell $ singleton $
                    "movq $" ++ (if b then "1" else "0") ++ ", " ++ show loc
                VString s -> do
                    modify $ (liftStrings (s:)) . (liftNStrings (+1))
                    n <- gets n_strings
                    tell $ singleton $ "movq _s" ++ show n ++ ", " ++ show loc
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
                (sstr, ntloc) <- case val of
                    Var var2 -> do
                        scol <- getColor var2
                        sloc <- getLocationErr scol
                        ntloc <- case (tloc, sloc) of
                            (MemRel _, MemRel _) -> swapToRegister quads tcol
                            (MemRel _, _) | op == OMul -> swapToRegister quads tcol
                            _ -> return tloc
                        return (show sloc, ntloc)
                    VInt int | op == OMul -> return ("$" ++ show int ++ ", " ++ show tloc, tloc)
                    VInt int -> return ("$" ++ show int, tloc)
                    VBool b -> return ("$" ++ if b then "1" else "0", tloc)
                    VString str -> do
                        modify $ (liftStrings (str:)) . (liftNStrings (+1))
                        n <- gets n_strings
                        return ("_s" ++ show n, tloc)
                    VStrRef _ -> error "string operation not allowed here"
                case op of
                    OAdd -> tell $ singleton $ "addq " ++ sstr ++ ", " ++ show ntloc
                    OSub -> tell $ singleton $ "subq " ++ sstr ++ ", " ++ show ntloc
                    OMul -> tell $ singleton $ "imulq " ++ sstr ++ ", " ++ show ntloc
                    OLTH -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setl " ++ showb ntloc]
                    OLE -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setle " ++ showb ntloc]
                    OGTH -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setg " ++ showb ntloc]
                    OGE -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setge " ++ showb ntloc]
                    OEQU -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "sete " ++ showb ntloc]
                    ONE -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setne " ++ showb ntloc]
                    _ -> error $ "operation " ++ show op ++ " not allowed here"
            compileDiv var val1 op val2 = do
                tloc <- getColor var >>= assignLocation
                locs <- gets locations
                if not (elem (Reg RDX) locs) && (tloc /= Reg RDX || op == ODiv) then
                    tell $ singleton $ "pushq %rdx"
                else return ()
                if not (elem (Reg RAX) locs) && (tloc /= Reg RAX || op == OMod) then
                    tell $ singleton $ "pushq %rax"
                else return ()
                case val1 of
                    Var v -> do
                        scol <- getColor v
                        sloc <- getLocationErr scol
                        if sloc /= Reg RAX then
                            tell $ singleton $ "movq " ++ show sloc ++ ", %rax"
                        else return ()
                    VInt int -> tell $ singleton $ "movq $" ++ show int ++ ", %rax"
                    _ -> error "not supported div operand"
                tell $ fromList ["movq $" ++ show ((2^(63::Integer))::Integer) ++ ", %rdx",
                                "andq %rax, %rdx",
                                "andq $" ++ show ((2^(63::Integer) - 1)::Integer) ++ ", %rax"]
                case val2 of
                    Var v -> do
                        scol <- getColor v
                        sloc <- getLocationErr scol
                        tell $ singleton $ "idivq " ++ show sloc
                    VInt int -> tell $ singleton $ "idivq $" ++ show int
                    _ -> error "not a div operand"
                case op of
                    ODiv | tloc == Reg RAX -> return ()
                    ODiv -> tell $ singleton $ "movq %rax, " ++ show tloc
                    OMod | tloc == Reg RDX -> return ()
                    OMod -> tell $ singleton $ "movq $rdx, " ++ show tloc
                    _ -> error "not a div operator"
                if not (elem (Reg RAX) locs) && (tloc /= Reg RAX || op == OMod) then
                    tell $ singleton $ "popq %rax"
                else return ()
                if not (elem (Reg RDX) locs) && (tloc /= Reg RDX || op == ODiv) then
                    tell $ singleton $ "popq %rdx"
                else return ()
            compileConcat var val1 val2 =
                compileQuadruple (QCall (Var var) (Ident "_concat") [val1, val2])
        QNeg (Var var) val -> do
            tloc <- getColor var >>= assignLocation
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr
                    if sloc /= tloc then
                        tell $ singleton $ "movq " ++ show sloc ++ ", " ++ show tloc
                    else return ()
                    tell $ fromList ["notq " ++ show tloc, "addq $1, " ++ show tloc]
                VInt int -> tell $ singleton $ "movq $" ++ show (-int) ++ ", " ++ show tloc
                _ -> error $ "cannot negate " ++ show val
        QNot (Var var) val -> do
            tloc <- getColor var >>= assignLocation
            case val of
                Var v -> do
                    sloc <- getColor v >>= getLocationErr
                    if sloc /= tloc then
                        tell $ singleton $ "movq " ++ show sloc ++ ", " ++ show tloc
                    else return ()
                    tell $ singleton $ "notq " ++ show tloc
                VBool b -> tell $ singleton $ "movq $" ++ (if b then "0" else "1") ++
                                            ", " ++ show tloc
                _ -> error $ "cannot not " ++ show val
        QIf val1 op val2 label -> do
            str1 <- valToStr val1
            str2 <- valToStr val2
            case op of
                OLTH -> tell $ fromList ["cmpq " ++ str1 ++ ", " ++ str2, "jlt " ++ show label]
                OLE -> tell $ fromList ["cmpq " ++ str1 ++ ", " ++ str2, "jle " ++ show label]
                OGTH -> tell $ fromList ["cmpq " ++ str1 ++ ", " ++ str2, "jgt " ++ show label]
                OGE -> tell $ fromList ["cmpq " ++ str1 ++ ", " ++ str2, "jge " ++ show label]
                OEQU -> case val1 of
                    VString str -> return () --TODO string compare
                    VStrRef var -> return () --TODO string compare
                    _ -> tell $ fromList ["cmpq " ++ str1 ++ ", " ++ str2, "jeq " ++ show label]
                ONE -> case val1 of
                    VString str -> return () --TODO string compare
                    VStrRef var -> return () --TODO string compare
                    _ -> tell $ fromList ["cmpq " ++ str1 ++ ", " ++ str2, "jne " ++ show label]
                _ -> error $ "not an if operation: " ++ show op
            where
            valToStr val = case val of
                Var var -> show <$> (getColor var >>= getLocationErr)
                VInt int -> return $ "$" ++ show int
                VBool b -> return $ if b then "$1" else "$0"
                VString str -> do
                    modify $ (liftStrings (str:)) . (liftNStrings (+1))
                    n <- gets n_strings
                    return $ "_s" ++ show n
                VStrRef v -> valToStr (Var v)
        QJmp label -> tell $ singleton $ "jmp " ++ show label
        QLabel label -> tell $ singleton $ show label ++ ":"
        QCall (Var var) (Ident fun) args -> do
            locs <- gets locations
            tcol <- getColor var
            tloc <- assignLocation tcol
            if not (elem (Reg RAX) locs) && tloc /= Reg RAX then
                tell $ singleton $ "pushq %rax"
            else return ()
            mapM_ compilePush (reverse args)
            tell $ singleton $ "call " ++ fun
            if tloc /= Reg RAX then
                tell $ singleton $ "movq %rax, " ++ show tloc
            else return ()
            if args /= [] then
                tell $ singleton $ "addq $rsp, " ++ show (8 * length args)
            else return ()
            if not (elem (Reg RAX) locs) && tloc /= Reg RAX then
                tell $ singleton $ "popq %rax"
            else return ()
            where
            compilePush val = do
                case val of
                    Var v -> do
                        sloc <- getColor v >>= getLocationErr
                        tell $ singleton $ "pushq " ++ show sloc
                    VInt int -> tell $ singleton $ "pushq $" ++ show int
                    VBool b -> tell $ singleton $ "pushq $" ++ (if b then "1" else "0")
                    VStrRef v -> compilePush (Var v)
                    VString str -> do
                        modify $ (liftStrings (str:)) . (liftNStrings (+1))
                        n <- gets n_strings
                        tell $ singleton $ "pushq _s" ++ show n
        QRet val -> do
            case val of
                Var v -> do
                    loc <- getColor v >>= getLocationErr
                    tell $ singleton $ "movq " ++ show loc ++ ", %rax"
                VInt int -> tell $ singleton $ "movq $" ++ show int ++ ", %rax"
                VBool b -> tell $ singleton $ "movq $" ++ (if b then "1" else "0") ++ ", %rax"
                VString str ->do
                    modify $ (liftStrings (str:)) . (liftNStrings (+1))
                    n <- gets n_strings
                    tell $ singleton $ "movq _s" ++ show n ++ ", %rax"
                VStrRef v -> compileQuadruple (QRet (Var v))
            used_regs <- (map ("popq " ++)) <$> (map show) <$> reverse <$>
                    usedRegisters <$> gets locations
            tell $ fromList used_regs
            tell $ fromList ["popq %rbp", "ret"]
        QRetV -> do
            used_regs <- (map ("popq " ++)) <$> (map show) <$> reverse <$>
                    usedRegisters <$> gets locations
            tell $ fromList used_regs
            tell $ fromList ["popq %rbp", "ret"]
        _ -> error "wrong quadruple"

swapToRegister :: [Quadruple] -> Color -> Result Location
swapToRegister quads c = do
    cmap <- asks coloring
    sloc <- getLocationErr c
    (_, regc, treg) <- gets $ maximum .
        (map (\(reg,col) -> (nextUse cmap col quads, col, reg))) . Map.assocs . register_colors
    let tloc = Reg treg
    tell $ fromList ["xorq " ++ show sloc ++ ", " ++ show tloc
                    , "xorq " ++ show tloc ++ ", " ++ show sloc
                    , "xorq " ++ show sloc ++ ", " ++ show tloc]
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

