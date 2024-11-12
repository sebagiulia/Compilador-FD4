{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import Subst
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode deriving Show
type Stack = [Val]
type Env = [Val]

{- Esta nueva representación de Bytecode es simplemente una lista de
   Word32.  La razón de usar Word32 es que es más fácil de manipular
   que Word8, y no hay razón para usar un tamaño de palabra más
   chico. -}

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern IFZ      = 16
pattern TAILCALL = 17

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (IFZ:xs)         = "IFZ" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = (show x): showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc term = do bc <- bcc' term 
              let (_,bc_clean) = span (==DROP) (reverse bc)
              return $ reverse bc_clean ++ [STOP]

bcc' :: MonadFD4 m => TTerm -> m Bytecode
bcc' (Const i (CNat n)) = return [CONST, n]
bcc' (V i (Bound n)) = return [ACCESS, n]
bcc' (V i (Free _)) = undefined
bcc' (V i (Global _)) = undefined
bcc' (Lam i n ty (Sc1 t')) = do b <- tcc t'
                                return $ [FUNCTION, length b] ++ b
bcc' (App i t1 t2) = do b1 <- bcc' t1
                        b2 <- bcc' t2
                        return $ b1 ++ b2 ++ [CALL]
bcc' (BinaryOp i op t1 t2) = do b1 <- bcc' t1
                                b2 <- bcc' t2
                                return $ b1 ++ b2 ++ [binop2bc op]
bcc' (Let i n ty t1 (Sc1 t2)) = do b1 <- bcc' t1
                                   b2 <- bcc' t2
                                   return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]
bcc' (Fix i f ty1 x ty2 (Sc2 t')) = do b <- bcc' t'
                                       return $ [FUNCTION, length b + 1] ++ b ++ [RETURN, FIX]
bcc' (IfZ i c t1 t2) = do c' <- bcc' c
                          t1' <- bcc' t1
                          t2' <- bcc' t2
                          let th = [FUNCTION, length t1' + 1] ++ t1' ++ [RETURN]
                          let el = [FUNCTION, length t2' + 1 ] ++ t2' ++ [RETURN]
                          return $ el ++ th ++ c' ++ [IFZ]
bcc' (Print i str arg) = do arg' <- bcc' arg
                            return $  arg' ++ [PRINT] ++ string2bc str ++ [NULL] ++ [PRINTN]

tcc :: MonadFD4 m => TTerm -> m Bytecode
tcc (App i t1 t2) = do bt1 <- bcc' t1
                       bt2 <- bcc' t2
                       return $ bt1 ++ bt2 ++ [TAILCALL]
tcc (IfZ i c t1 t2) = do c' <- bcc' c
                         t1' <- tcc t1
                         t2' <- tcc t2
                         return $ c' ++ [JUMP, length t1'] ++ t1' ++ t2'
tcc (Let i n ty t1 (Sc1 t2)) = do b1 <- bcc' t1
                                  t2' <- tcc t2
                                  return $ b1 ++ [SHIFT] ++ t2'
tcc t = do tt <- bcc' t
           return $ tt ++ [RETURN]

binop2bc :: BinaryOp -> Opcode
binop2bc Add = ADD
binop2bc Sub = SUB

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule [] = return []
bytecompileModule m = bcc (foldl f (declBody (m!!0)) (drop 1 m))
                      where f tt (Decl i _ n ty _ tm) = Let (i,ty) n ty tm (close n (globalToFree n tt))

-- intercambia variables globales por variables libres
globalToFree :: Name -> Tm info Var -> Tm info Var
globalToFree nm t' = case t' of
   V p (Global x) -> if x == nm then V p (Free nm) else V p (Global x) 
   V p (Bound i) -> V p (Bound i)
   V p (Free x) -> V p (Free x)
   Lam p x ty (Sc1 t) -> Lam p x ty (Sc1 (globalToFree nm t))
   App p t1 t2 -> App p (globalToFree nm t1) (globalToFree nm t2)
   Fix p f fty x xty (Sc2 t) -> Fix p f fty x xty (Sc2 (globalToFree nm t))
   IfZ p c t e -> IfZ p (globalToFree nm c) (globalToFree nm t) (globalToFree nm e)
   Const p cn -> Const p cn
   Print p str t -> Print p str (globalToFree nm t)
   BinaryOp p op t1 t2 -> BinaryOp p op (globalToFree nm t1) (globalToFree nm t2)
   Let p x ty t1 (Sc1 t2) -> Let p x ty (globalToFree nm t1) (Sc1 (globalToFree nm t2))

-- | Toma un bytecode, lo codifica y lo escribe en un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = macchina bc [] []

macchina :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
macchina (CONST:n:cs) e s = macchina cs e (I n:s)
macchina (ADD:cs) e ((I a):(I b):s) = macchina cs e ((I (a+b)):s)
macchina (SUB:cs) e ((I a):(I b):s) = macchina cs e (I (max 0 (b - a)):s)
macchina (ACCESS:n:cs) e s = macchina cs e ((e!!n):s)
macchina (CALL:cs) e (v:Fun e' bc':s) = macchina bc' (v:e') ((RA e cs):s)
macchina (FUNCTION:n:cs) e s = macchina (drop n cs) e (Fun e (take n cs):s)
macchina (RETURN:_) _ (v:RA e bc:s) = macchina bc e (v:s)
macchina (FIX:cs) e ((Fun e' cf):s) = do let efix = (Fun efix cf): e'
                                         macchina cs e ((Fun efix cf):s)
macchina (SHIFT:cs) e (v:s) = macchina cs (v:e) s
macchina (DROP:cs) e s = macchina cs (tail e) s
macchina (PRINTN:cs) e ((I n):s) = do printLnFD4 (show n)
                                      macchina cs e ((I n):s)
macchina (PRINT:cs) e s = do let str = takeWhile (/=NULL) cs
                             printFD4 $ bc2string str
                             macchina (drop (length str) cs) e s
macchina (NULL:cs) e s = macchina cs e s
macchina (IFZ:cs) e ( I 0 : Fun e1 c1 : _ : s) = macchina c1 e1 (RA e cs:s)
macchina (IFZ:cs) e ( I _ : _ : Fun e2 c2 : s) = macchina c2 e2 (RA e cs:s)
macchina (JUMP:_:cs) e (I 0:s) = macchina cs e s
macchina (JUMP:n:cs) e (I _:s) = macchina (drop n cs) e s
macchina (TAILCALL:_) _ (v:Fun e' bc':s) = macchina bc' (v:e') s
macchina (STOP:cs) e s = return ()
macchina (c:_) e s = failFD4 $ "Instrucción inválida en la Macchina: " ++ head (showOps [c])
macchina [] e s = failFD4 "No hay más instrucciones en la Macchina"