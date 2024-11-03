{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
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
showOps (IFZ:xs)           = "IFZ" : showOps xs
showOps (x:xs)           = (show x): showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc term = bcc' term >>= return . (++ [STOP])
 where bcc' t = case t of
        Const i (CNat n) -> return [CONST, n]
        V i v -> case v of
          Free n -> undefined
          Global n -> undefined
          Bound n -> return [ACCESS, n]
        Lam i n ty (Sc1 t') -> do b <- bcc' t'
                                  return $ [FUNCTION, length b + 1] ++ b ++ [RETURN]
        App i t1 t2 -> do b1 <- bcc' t1
                          b2 <- bcc' t2
                          return $ b1 ++ b2 ++ [CALL]
        BinaryOp i op t1 t2 -> do b1 <- bcc' t1
                                  b2 <- bcc' t2
                                  return $ b1 ++ b2 ++ [binop2bc op]
        Let i n ty t1 (Sc1 t2) -> do b1 <- bcc' t1
                                     b2 <- bcc' t2
                                     return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]
        Fix i f ty1 x ty2 (Sc2 t') -> do b <- bcc' t'
                                         return $ [FUNCTION, length b + 1] ++ b ++ [RETURN, FIX]   
        IfZ i c t1 t2 -> do c' <- bcc' c
                            t1' <- bcc' t1
                            t2' <- bcc' t2
                            let th = [FUNCTION, length t1' + 1] ++ t1' ++ [RETURN]
                            let el = [FUNCTION, length t2' + 1 ] ++ t2' ++ [RETURN]
                            return $ el ++ th ++ c' ++ [IFZ] 
        Print i str arg -> do arg' <- bcc' arg
                              return $ [PRINT] ++ (string2bc str) ++ [NULL] ++ arg' ++ [PRINTN]

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
bytecompileModule m = bcc (foldr f (declBody neutro) (take (length m - 1) m))
                      where neutro = m!!(length m - 1)
                            f (Decl i _ n ty _ tm) tt = Let (i,ty) n ty tm (close n tt)

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
macchina (CONST:n:cs) e s = macchina cs e ((I n):s)
macchina (ADD:cs) e ((I a):(I b):s) = macchina cs e ((I (a+b)):s) 
macchina (SUB:cs) e ((I a):(I b):s) = macchina cs e ((I ((max 0 (a-b)))):s)
macchina (ACCESS:n:cs) e s = macchina cs e ((e!!n):s)
macchina (CALL:cs) e (v:Fun e' bc':s) = macchina bc' (v:e') ((RA e cs):s)
macchina (FUNCTION:n:cs) e s = macchina (drop n cs) e (Fun e (take n cs):s)
macchina (RETURN:_) _ (v:RA e bc:s) = macchina bc e (v:s)
macchina (FIX:cs) e ((Fun e' cf):s) = do let efix = (Fun efix cf): e'
                                         macchina cs e ((Fun efix cf):s) 
macchina (SHIFT:cs) e (v:s) = macchina cs (v:e) s
macchina (DROP:cs) e s = macchina cs (tail e) s
macchina (PRINTN:cs) e ((I n):s) = do printFD4 (show n)
                                      macchina cs e ((I n):s)
macchina (PRINT:cs) e s = do let str = takeWhile (/=NULL) cs
                             printFD4 $ bc2string str
                             macchina (drop (length str) cs) e s
macchina (NULL:cs) e s = macchina cs e s
macchina (STOP:cs) e s = printFD4 (show (head s))
macchina (IFZ:cs) e ( I 0 : Fun e1 c1 : _ : s) = macchina c1 e1 (RA e cs:s)
macchina (IFZ:cs) e ( I _ : _ : Fun e2 c2 : s) = macchina c2 e2 (RA e cs:s)
macchina (c:_) e s = failFD4 $ "Instrucción inválida en la Macchina: " ++ (show c)
macchina [] e s = failFD4 "No hay más instrucciones en la Macchina"