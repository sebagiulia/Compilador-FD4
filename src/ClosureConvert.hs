module ClosureConvert where

import IR
import Lang
import MonadFD4
import Control.Monad.Writer

ty2irty :: Ty -> IrTy
ty2irty NatTy = IrInt
ty2irty (FunTy t1 t2) = IrFunTy

findIrDecl :: Name -> IrDecl -> Bool
findIrDecl name (IrFun n _ _ b) = n == name
findIrDecl _ _ = False

closureConvert :: TTerm -> [Ir] -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free x)) _ = return $ IrVar x
closureConvert (V _ (Global x)) _ = return $ IrGlobal x
closureConvert (Const _ c) _ = return $ IrConst c
closureConvert (Lam _ x ty t) vars = do
  t' <- closureConvert (open x t) (IrVar x:vars)
  n <- get  
  let fresh = "__g" ++ show n
  modify (+1)
  let irty = ty2irty $ getTy t
  let dec = IrFun fresh irty [(x,ty2irty ty)] t'
  tell [dec]
  return $ MkClosure fresh vars
closureConvert (App _ t u) vars = do
  (t', decls) <- listen $ closureConvert t vars
  u' <- closureConvert u
  case t' of 
    IrGlobal x -> do 
      let (IrVal _ ty (MkClosure name vars)) = find (findIrDecl x) decls
      return $ (IrCall (IrVar name) [vars++u']) ty
    MkClousure name vars -> do
      return $ (IrCall (IrVar name) [u':vars])
    _ -> undefined --------------------------------------------------------------------------------- arreglar
closureConvert (Print _ str t) _ = do
  t' <- closureConvert t
  return $ IrPrint str t'
closureConvert (BinaryOp _ op t u) _ = do
  t' <- closureConvert t
  u' <- closureConvert u
  return $ IrBinaryOp op t' u'
closureConvert (Fix _ f fty x xty t) vars = do
  n <- get  
  let fresh = "__g" ++ show n
  let fvf = "__f"++ show n
  let fvx = "__x"++ show n
  modify (+1)
  t' <- closureConvert (open2 fvf fvx t) (IrVar fvx:IrVar fvf:vars)
  let irty = ty2irty $ getTy t
  let dec = IrFun fresh irty [(f,ty2irty fty), (x,ty2irty ty)] t' 
  tell [dec]
  return $ MkClosure fresh vars

closureConvert (IfZ _ c t e) _ = do
  c' <- closureConvert c
  t' <- closureConvert t
  e' <- closureConvert e
  return $ IrIfz c' t' e'
closureConvert (Let _ x ty t u) _ = undefined


runCC :: [Decl TTerm] -> [IrDecl]
runCC a = undefined



{- 
 
 let suma = lam x -> lam y -> x + y
            
  runCC [suma] =
    [IrVal suma (MkClousure _g1 []).
     IrFun _g1 ["x"] (MkClosure _g0 [x]),
     IrFun _g0 ["y", "x"] (BinaryOP (Free "y") (Free "x"))]



 let suma5 = (Global "suma") 5 
 

 fd4fun suma;
 fd4fun _g1(int x) { 
    return fd4_mkclosure(_g0, 1, x);
 }
 int _g0(int y, clos) { 
    return y + x;
 }

 int main() {
  
  suma = fd4_mkclosure(_g1, 0);
  
  return 0;
 }

=========================================
let id = lam x -> x
let cinco = id 5
runCC [id] =
  [IrVal id (MkClosure _g0 []),
   IrFun _g0 Int ["x"] (IrVar "x"),
   IrVal cinco (IrCall (IrVar "_g0") [Const 5])
  ]

fd4fun id;
int _g0(int x) {
  return x
} 
int cinco;

int main() {
  id = fd4_mkclosure(_g0, 0);
  cinco = (int)((fd4fun)_g0(5));
  return 0;
}

 -} 