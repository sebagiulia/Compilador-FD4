module ClosureConvert where

import IR
import Lang
import MonadFD4

ty2irty :: Ty -> IrTy
ty2irty NatTy = IrInt
ty2irty (FunTy t1 t2) = IrFunTy (ty2irty t1) (ty2irty t2)

closureConvert :: TTerm -> [Ir] -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free x)) _ = return $ IrVar x
closureConvert (V _ (Global x)) _ = return $ IrGlobal x
closureConvert (Const _ c) _ = return $ IrConst c
closureConvert (Lam _ x ty (Sc1 t)) vars = do
  n <- get  
  let fresh = "__g" ++ show n
  modify (+1)
  t' <- closureConvert t (IrVar x:vars)
  let irty = ty2irty $ getTy t
  let dec = IrFun fresh irty [(x,ty2irty ty)] t' 
  tell [dec]
  return $ MkClosure fresh vars
closureConvert (App _ t u) vars = do
  (t'@(MkClosure name v), decls) <- listen $ closureConvert t vars
  u' <- closureConvert u
  return $ IrLet "clos" IrCLo t' (IrCall  (u':decls) )
closureConvert (Print _ str t) = do
  t' <- closureConvert t
  return $ IrPrint str t'
closureConvert (BinaryOp _ op t u) = do
  t' <- closureConvert t
  u' <- closureConvert u
  return $ IrBinaryOp op t' u'
closureConvert (Fix _ f fty x xty t) = undefined
closureConvert (IfZ _ c t e) = do
  c' <- closureConvert c
  t' <- closureConvert t
  e' <- closureConvert e
  return $ IrIfz c' t' e'
closureConvert (Let _ x ty t u) = do


runCC :: [Decl TTerm] -> [IrDecl]


