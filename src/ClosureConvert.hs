module ClosureConvert where

import IR
import Lang
import Subst
import MonadFD4
import Control.Monad.Writer

ty2irty :: Ty -> IrTy
ty2irty NatTy = IrInt
ty2irty (FunTy t1 t2) = IrClo

findIrDecl :: Name -> IrDecl -> Bool
findIrDecl name (IrFun n _ _ b) = n == name
findIrDecl _ _ = False

makeletirs :: [(Ir, IrTy)] -> Ir -> Int -> Ir
makeletirs [] t _ = t
makeletirs (((IrVar x),ty):xs) t n = IrLet x ty (IrAccess (IrVar "clos") ty n) (makeletirs xs t (n+1))
makeletirs _ _ _ = undefined

makeletrec :: Name -> Ir -> Ir
makeletrec name = IrLet name IrClo (IrVar "clos")

closureConvert :: TTerm -> [(Ir, IrTy)] -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Bound i)) _ = undefined
closureConvert (V _ (Free x)) _ = return $ IrVar x
closureConvert (V _ (Global x)) _ = return $ IrGlobal x
closureConvert (Const _ c) _ = return $ IrConst c
closureConvert (Lam _ _ ty t) vars = do
  n <- get
  let x = "__x" ++ show n
  let fresh = "__g" ++ show n
  let ot = open x t
  modify (+1)
  t' <- closureConvert ot ((IrVar x, ty2irty ty):vars)
  let irty = ty2irty $ getTy ot
  let dec = IrFun fresh irty [("clos", IrClo), (x,ty2irty ty)] (makeletirs vars t' 1)
  tell [dec]
  return $ MkClosure fresh (map fst vars)
closureConvert (App (_, ty) t u) vars = do
  clo <- closureConvert t vars
  u' <- closureConvert u vars
  n <- get
  modify (+1)
  let fresh = "_clos" ++ show n 
  return $ IrLet fresh IrClo clo $ IrCall (IrAccess (IrVar fresh) IrFunTy 0) [IrVar fresh, u'] (ty2irty ty)
closureConvert (Print (_, ty) str t) vars = do
  n <- get
  let fresh = "_print" ++ show n
  modify (+1)
  t' <- closureConvert t vars
  return $ IrLet fresh (ty2irty ty) t' $ IrPrint str (IrVar fresh)
closureConvert (BinaryOp _ op t u) vars = do
  t' <- closureConvert t vars
  u' <- closureConvert u vars
  return $ IrBinaryOp op t' u'
closureConvert (Fix _ f fty _ xty t) vars = do
  n <- get
  let x = "__x" ++ show n
  let fresh = "__g" ++ show n
  let fresh2 = "rec"
  modify (+1)
  let ot = open2 fresh2 x t
  t' <- closureConvert ot ((IrVar fresh2, ty2irty fty):(IrVar x, ty2irty xty):vars)
  let irty = ty2irty $ getTy ot
  let dec = IrFun fresh irty [("clos", IrClo), (x,ty2irty xty)] (makeletrec fresh2 (makeletirs vars t' 1))
  tell [dec]
  return $ MkClosure fresh (map fst vars)
closureConvert (IfZ _ c t e) vars = do
  c' <- closureConvert c vars
  t' <- closureConvert t vars
  e' <- closureConvert e vars
  return $ IrIfZ c' t' e'
closureConvert (Let _ v ty t u) vars = do
  n <- get
  modify (+1)
  let x = "__x" ++ show n
  t' <- closureConvert t vars
  u' <- closureConvert (open x u) ((IrVar x, ty2irty ty):vars)
  return $ IrLet x (ty2irty ty) t' u'

runCC :: [Decl TTerm Ty] -> [IrDecl]
runCC decls = let (_, irDecls') = runWriter $ runStateT (mapM f (reverse decls)) 0
              in irDecls'
    where f (Decl _ _ n ty _ b) = do
            t' <- closureConvert b []
            let irval = IrVal n (ty2irty ty) t'
            tell [irval]
            return ()