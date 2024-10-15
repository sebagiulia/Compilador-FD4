{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then return $ V p (Free v)
    else return $ V p (Global v)
elab' _ (SConst p c) = return $ Const p c
elab' env (SLam p [(v, ty)] t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SLam p ((v, ty):args) t) = Lam p v ty (close v (elab' (v:env) (SLam p args t)))
elab' env (SLam p [] t) = undefined -- no entra nunca
elab' env (SFix p (f,fty) args@[(x,xty)] t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SFix p (f,fty) args@((x,xty):xs) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) (SLam p xs t)))
elab' env (SFix p f [] t) = undefined -- no entra nunca
elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str) = Lam i "x" NatTy (close "x" (Print i str (elab' ("x":env) (SV i "x"))))  -- Se encapsula en una expresión lambda
--elab' env (SPrint i str) = App i (Lam i "x" NatTy (close "x" (Print i str (elab' ("x":env) (SV i "x"))))) (Const i (CNat 0))  -- Se encapsula en una expresión lambda
-- Aplicaciones generales
elab' env (SApp p (SPrint i str) a) = Print i str (elab' env a)
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)
elab' env (SLet p (v,vty) def body) =  
  Let p v vty (elab' env def) (close v (elab' (v:env) body))
elab' env (SLetFun p False (f, fty) args t1 t2) = Let p f (foldr typeConverter fty args) (elab' env (SLam p args t1)) (close f (elab' (f:env) t2)) 
elab' env (SLetFun p True (f, fty) args t1 t2) =  Let p f (foldr typeConverter fty args) (elab' env (SFix p (f,foldr typeConverter fty args) args t1)) (close f (elab' (f:env) t2))

elabDecl :: Decl STerm -> Decl Term
elabDecl d@(Decl _ _ _ _ [] _) = fmap elab d
elabDecl d@(Decl p False f fty args t) = fmap elab (Decl p True f (foldr typeConverter fty args) [] (SLam p args t)) 
elabDecl d@(Decl p True f fty args t) = fmap elab (Decl p True f (foldr typeConverter fty args) [] (SFix p (f,(foldr typeConverter fty args)) args t)) 

elabDeclTy :: MonadFD4 m => DeclTy STy -> m DeclTy Ty
elabDeclTy d = undefined


elabTy :: MonadFD4 m => STy -> m Ty
elabTy SNatTy = return NatTy
elabTy (SFunTy a b) = do 
      sa <- elabTy a
      sb <- elabTy b
      return $ FunTy sa sb 
elabTy (SVarTy n) = 

typeConverter :: (Name, Ty) -> Ty -> Ty
typeConverter (_, t) tys = FunTy t tys


{-

SLet x: SNat -> HOLA -> SNat = f in f 5 6 7

-}
