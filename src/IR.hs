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






-}