module Compiler where

import qualified Data.Map.Strict as Map
import Data.DList(DList, singleton, toList, fromList)
import Control.Monad.RWS
import Quadruples
import AbsLatte

arch_registers :: Int
arch_registers = 14

newtype Register = Register Int
    deriving (Eq, Ord)

newtype MemOffset = MemOff Int
    deriving (Eq, Ord)

data Location = Reg Register | MemRel MemOffset
    deriving Eq

instance Show Location where
    show loc = case loc of
        Reg (Register 0) -> "%rbx"
        Reg (Register 1) -> "%rcx"
        Reg (Register 2) -> "%rsi"
        Reg (Register 3) -> "%rdi"
        Reg (Register 4) -> "%r8"
        Reg (Register 5) -> "%r9"
        Reg (Register 6) -> "%r10"
        Reg (Register 7) -> "%r11"
        Reg (Register 8) -> "%r12"
        Reg (Register 9) -> "%r13"
        Reg (Register 10) -> "%r14"
        Reg (Register 11) -> "%r15"
        Reg (Register 12) -> "%rdx"
        Reg (Register 13) -> "%rax"
        Reg _ -> error "unknown register"
        MemRel (MemOff n) -> (show n) ++ "(%ebp)"

showb :: Location -> String
showb loc = case loc of
    Reg (Register 0) -> "%bl"
    Reg (Register 1) -> "%cl"
    Reg (Register 2) -> "%sil"
    Reg (Register 3) -> "%dil"
    Reg (Register 4) -> "%r8b"
    Reg (Register 5) -> "%r9b"
    Reg (Register 6) -> "%r10b"
    Reg (Register 7) -> "%r11b"
    Reg (Register 8) -> "%r12b"
    Reg (Register 9) -> "%r13b"
    Reg (Register 10) -> "%r14b"
    Reg (Register 11) -> "%r15b"
    Reg (Register 12) -> "%dl"
    Reg (Register 13) -> "%al"
    Reg _ -> error "unknown register"
    MemRel (MemOff n) -> (show (n + 7)) ++ "(%ebp)"

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

getMaybeColor :: Location -> Result (Maybe Color)
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
        QOp (Var var) val1 op val2 -> do
            if op == Div || op == Mod then compileDiv var val1 op val2
            else if op == Concat then compileConcat var val1 op val2
            else do
                tcol <- getColor var
                tloc <- assignLocation tcol
                mcol1 <- getMaybeColor val1
                mcol2 <- getMaybeColor var2
                case mcol1 of
                    Just col1 | col1 == tcol -> do
                        compileQuadruple (QAss (Var var) val1)
                        compileOperation var op val2
                    _ -> case mcol2 of
                        Just col2 | col2 == tcol -> case op of
                            Sub -> do
                                compileQuadruple (QNeg (Var var) val2)
                                compileOperation var Add val1
                            LTH -> swapOrder GTH
                            LE -> swapOrder GE
                            GTH -> swapOrder LTH
                            GE -> swapOrder LE
                            _ -> swapOrder op
                            where
                            swapOrder o = do
                                compileQuadruple (QAss (Var var) var2)
                                compileOperation var o var1
                        _ -> do
                            compileQuadruple (QAss (Var var) val1)
                            compileOperation var op val2
            where
            compileOperation var op val = do
                tcol <- getColor var
                tloc <- assignLocation tcol
                (sstr, ntloc) <- case val2 of
                    Var var2 -> do
                        scol <- getColor var2
                        sloc <- getLocationErr scol
                        tloc <- case (tloc, sloc) of
                            (MemRel _, MemRel _) -> swapToRegister quads tcol
                            (MemRel _, _) | op == Mul -> swapToRegister quads tcol
                            _ -> return tloc
                        return (show sloc, tloc)
                    VInt int | op == Mul -> return ("$" ++ show int ++ ", " ++ show tloc, tloc)
                    VInt int -> return ("$" ++ show int, tloc)
                    VBool b -> return ("$" ++ if b then "1" else "0", tloc)
                    VString str -> do
                        modify $ (liftStrings (str:)) . (liftNStrings (+1))
                        n <- gets n_strings
                        return ("_s" ++ show n, tloc)
                    VStrRef _ -> error "string operation not allowed here"
                case op of
                    Add -> tell $ singleton $ "addq " ++ sstr ++ ", " ++ show ntloc
                    Sub -> tell $ singleton $ "subq " ++ sstr ++ ", " ++ show ntloc
                    Mul -> tell $ singleton $ "imulq " ++ sstr ++ ", " ++ show ntloc
                    And -> tell $ singleton $ "andq " ++ sstr ++ ", " ++ show ntloc
                    Or -> tell $ singleton $ "orq " ++ sstr ++ ", " ++ show ntloc
                    LTH -> tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setl " ++ showb ntloc]
                    LE ->tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setle " ++ showb ntloc]
                    GTH ->tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setg " ++ showb ntloc]
                    GE ->tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setge " ++ showb ntloc]
                    EQU ->tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "sete " ++ showb ntloc]
                    NE ->tell $ fromList ["cmp " ++ show ntloc ++ ", " ++ sstr,
                                            "setne " ++ showb ntloc]
                    _ -> error $ "operation " ++ show op ++ " not allowed here"
            compileDiv var val1 op val2 =
            compileConcat var val1 op val2 =
        QNeg val1 val2 -> return ()
        QNot val1 val2 -> return ()
        QIf val1 op val2 label -> return ()
        QJmp label -> return ()
        QLabel label -> return ()
        QPush val -> return ()
        QCall val ident -> return ()
        QRet val -> return ()
        QRetV -> return ()
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

