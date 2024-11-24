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
  (t', decls) <- listen $ closureConvert t vars
  u' <- closureConvert u
  case t' of 
    IrGlobal x -> do 
      let (IrVal _ _ def) = find (findIrDecl x) decls
      return $ IrLet "clos" IrClo def (IrCall )
  return $ IrLet "clos" IrCLo t' (IrCall body (u':vars))
closureConvert (Print _ str t) _ = do
  t' <- closureConvert t
  return $ IrPrint str t'
closureConvert (BinaryOp _ op t u) _ = do
  t' <- closureConvert t
  u' <- closureConvert u
  return $ IrBinaryOp op t' u'
closureConvert (Fix _ f fty x xty t) _ = undefined
closureConvert (IfZ _ c t e) _ = do
  c' <- closureConvert c
  t' <- closureConvert t
  e' <- closureConvert e
  return $ IrIfz c' t' e'
closureConvert (Let _ x ty t u) _ = undefined


runCC :: [Decl TTerm] -> [IrDecl]
runCC a = undefined

