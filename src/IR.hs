module IR where

import Lang

data Ir = IrVar Name
        | IrGlobal Name
        | IrCall Ir [Ir] IrTy
                        -- ^ Tipo de expr final
        | IrConst Const
        | IrPrint String Ir
        | IrBinaryOp BinaryOp Ir Ir 
        | IrLet Name IrTy Ir Ir
        | IrIfZ Ir Ir Ir
        | MkClosure Name [Ir]
        | IrAccess Ir IrTy Int
  deriving Show

data IrTy = IrInt
          | IrClo
          | IrFunTy
  deriving Show

data IrDecl =
    IrFun { irDeclName :: Name
          , irRetTy :: IrTy
          , irDeclArgs :: [(Name, IrTy)]
          , irDeclBody :: Ir
    }
  | IrVal { irDeclName :: Name
          , irDeclTy :: IrTy
          , irDeclDef :: Ir
          }
  deriving Show

newtype IrDecls = IrDecls { irDecls :: [IrDecl] }

{-
La siguiente instancia es sólo para debugging
-}
instance Show IrDecls where
  show (IrDecls decls) =
   concatMap (\d -> show d ++ "\n") decls


{-

let id (x:Nat) : Nat = x
          
          |
          |
          v

let _g0 : Nat = e0

_g0(clos, x) = x

let id (x : Nat) : Nat = _g0[x]

          |
          |
          v

IrFun _g0 Nat [("x",Nat)] (IrVar x)


 
IrVal id Nat (MakeClosure _g0 [] Nat)

id 3

irCall (Global id) 3 Nat

g0 [3]






let suma : Nat -> (Nat -> Nat) =
  fun (x:Nat) ->
    fun (y:Nat) -> 
      fun (z:Nat) -> x + y + z 

let suma5 : Nat -> Nat = suma 5

              |
              |
              | Closure convert
              |
              |
              v

let _g0 (z:Nat): Nat -> e0 + e1 + z

let suma : Nat -> (Nat -> Nat) =
  fun (x:Nat) ->
    fun (y:Nat) -> _g0[x, y] 

let suma5 : Nat -> Nat = suma 5


              |
              |
              | Closure convert
              |
              |
              v

let _g0 (z:Nat): Nat = e0 + e1 + z
let _g1 (y:Nat): Nat -> Nat = _g0[x, y]

let suma : Nat -> (Nat -> Nat) =
  fun (x:Nat) -> _g1[x] 


              |
              |
              | Hoisting pt1
              |
              |
              v

let _g0 (z:Nat): Nat = e0 + e1 + z
let _g1 (y:Nat): Nat -> Nat = _g0[y, x]
let _g2 (x:Nat): Nat -> Nat -> Nat = _g1[x] 
let suma : Nat -> (Nat -> Nat -> Nat) = _g2[]

let suma5 : Nat -> Nat = suma 5



-}