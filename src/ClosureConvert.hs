module ClosureConvert where

import IR
import Lang
import Subst
import MonadFD4
import Control.Monad.Writer

ty2irty :: Ty -> IrTy
ty2irty NatTy = IrInt
ty2irty (FunTy t1 t2) = IrFunTy

findIrDecl :: Name -> IrDecl -> Bool
findIrDecl name (IrFun n _ _ b) = n == name
findIrDecl _ _ = False

makeletirs :: [(Ir, IrTy)] -> Ir -> Int -> Ir
makeletirs [] t _ = t
makeletirs (((IrVar x),ty):xs) t n = IrLet x ty (IrAccess (IrVar "clos") ty n) (makeletirs xs t (n+1))
makeletirs _ _ _ = undefined 

closureConvert :: TTerm -> [(Ir, IrTy)] -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Bound i)) _ = undefined
closureConvert (V _ (Free x)) _ = return $ IrVar x
closureConvert (V _ (Global x)) _ = return $ IrGlobal x
closureConvert (Const _ c) _ = return $ IrConst c
closureConvert (Lam _ x ty t) vars = do
  let ot = open x t
  t' <- closureConvert ot ((IrVar x, ty2irty ty):vars) 
  n <- get  
  let fresh = "__g" ++ show n
  modify (+1)
  let irty = ty2irty $ getTy ot
  let dec = IrFun fresh irty [("clos", IrClo), (x,ty2irty ty)] (makeletirs vars t' 1) 
  tell [dec]
  return $ MkClosure fresh (map fst vars)
closureConvert (App (_, ty) t u) vars = do
  clo <- closureConvert t vars
  u' <- closureConvert u vars
  return $ (IrCall (IrAccess clo IrFunTy 0) [clo, u'] (ty2irty ty))
closureConvert (Print _ str t) vars = do
  t' <- closureConvert t vars
  return $ IrPrint str t'
closureConvert (BinaryOp _ op t u) vars = do
  t' <- closureConvert t vars
  u' <- closureConvert u vars
  return $ IrBinaryOp op t' u'
closureConvert (Fix _ f fty x xty t) vars = do
  n <- get  
  let fresh = "__g" ++ show n
  modify (+1)
  let ot = open2 f x t
  t' <- closureConvert ot ((IrVar f, ty2irty fty):(IrVar x, ty2irty xty):vars)
  let irty = ty2irty $ getTy ot
  let dec = IrFun fresh irty [("clos", IrClo), (x,ty2irty xty)] t' 
  tell [dec]
  return $ MkClosure fresh (map fst vars)
closureConvert (IfZ _ c t e) vars = do
  c' <- closureConvert c vars 
  t' <- closureConvert t vars 
  e' <- closureConvert e vars 
  return $ IrIfZ c' t' e'
closureConvert (Let _ x ty t u) vars = do
  t' <- closureConvert t vars
  u' <- closureConvert (open x u) ((IrVar x, ty2irty ty):vars)
  return $ IrLet x (ty2irty ty) t' u'


runCC :: [Decl TTerm Ty] -> [IrDecl]
runCC decls = let (_, irDecls') = runWriter $ runStateT (mapM f decls) 0
              in irDecls'
    where f (Decl _ _ n ty _ b) = do 
            t' <- closureConvert b [] 
            let irval = IrVal n (ty2irty ty) t' 
            tell [irval]
            return irval



{- 
 
 let suma = lam x -> lam y -> x + y
            
  runCC [suma] =
    [IrVal suma (MkClousure _g1 []).
     IrFun _g1 ["x"] (MkClosure _g0 [x]),
     IrFun _g0 ["y"] (IrBinaryOP (IrVar "y") (IrVar "x"))]



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