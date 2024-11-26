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

module Elab (elab, elabDecl, elabDeclTy) where

import Lang
import Subst
import MonadFD4
import PPrint (ppName)


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
elab' env (SLam p [(v, ty)] t) = do
    te <- elab' (v:env) t
    let tc = close v te
    tye <- elabTy ty
    return $ Lam p v tye tc 
elab' env (SLam p ((v, ty):args) t) = do
    te <- elab' (v:env) (SLam p args t)
    let tc = close v te
    tye <- elabTy ty
    return $ Lam p v tye tc
elab' env (SLam p [] t) = undefined -- no entra nunca
elab' env (SFix p (f,fty) args@[(x,xty)] t) = do 
    te <- elab' (x:f:env) t
    ftye <- elabTy fty
    xtye <- elabTy xty
    let tc = close2 f x te
    return $ Fix p f ftye x xtye tc
elab' env (SFix p (f,fty) args@((x,xty):xs) t) = do
    te <- elab' (x:f:env) (SLam p xs t)
    let tc = close2 f x te
    ftye <- elabTy fty
    xtye <- elabTy xty
    return $ Fix p f ftye x xtye tc 
elab' env (SFix p f [] t) = undefined -- no entra nunca
elab' env (SIfZ p c t e) = do
    cond <- elab' env c
    t1   <- elab' env t
    t2   <- elab' env e
    return $ IfZ p cond t1 t2
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do
    op1 <- elab' env t
    op2 <- elab' env u
    return $ BinaryOp i o op1 op2
-- Operador Print
elab' env (SPrint i str) = do
    arg <- elab' ("x":env) (SV i "x")
    let tc = close "x" (Print i str arg)
    return $ Lam i "x" NatTy tc  -- Se encapsula en una expresión lambda
-- Aplicaciones generales
elab' env (SApp p (SPrint i str) a) = do
    te <- elab' env a
    return $ Print i str te
elab' env (SApp p h a) = do 
    fun <- elab' env h
    arg <- elab' env a
    return $ App p fun arg
elab' env (SLet p (v,vty) def body) = do
    te <- elab' (v:env) body
    let tc = close v te
    tt <- elab' env def
    vtye <- elabTy vty
    return $ Let p v vtye tt tc
elab' env (SLetFun p False (f, fty) args t1 t2) = do
    te1 <- elab' env (SLam p args t1)
    te2 <- elab' (f:env) t2
    let tc = close f te2
    ftye <- elabTy (foldr stypeConverter fty args)
    return $ Let p f ftye te1 tc 
elab' env (SLetFun p True (f, fty) args t1 t2) = do 
    te2 <- elab' (f:env) t2
    let tc = close f te2
    te1 <- elab' env (SFix p (f,foldr stypeConverter fty args) args t1)
    ftye <- elabTy (foldr stypeConverter fty args)
    return $ Let p f ftye te1 tc

elabDecl :: MonadFD4 m => Decl STerm STy -> m (Decl Term Ty)
elabDecl d@(Decl p r n t [] b) = do 
    te <- elabTy t
    be <- elab b
    return $ Decl p r n te [] be
elabDecl d@(Decl p False f fty args t) = do 
    ftye <- elabTy $ foldr stypeConverter fty args
    te <- elab (SLam p args t)
    args' <- fmapArgs args
    return $ Decl p False f ftye args' te
elabDecl d@(Decl p True f fty args t) = do
    ftye <- elabTy $ foldr stypeConverter fty args
    args' <- fmapArgs args
    te <- elab (SFix p (f,(foldr stypeConverter fty args)) args t)
    return (Decl p True f ftye args' te) 

fmapArgs :: MonadFD4 m => [(Name, STy)] -> m [(Name, Ty)]
fmapArgs [] = return []
fmapArgs ((n,st):xs) = do t <- elabTy st
                          ts <- fmapArgs xs
                          return ((n,t):ts)

elabDeclTy :: MonadFD4 m => DeclTy STy -> m (DeclTy Ty)
elabDeclTy (DeclTy p n t) = do
    te <- elabTy t
    return $ DeclTy p n te 

elabTy :: MonadFD4 m => STy -> m Ty
elabTy SNatTy = return NatTy
elabTy (SFunTy a b) = do 
    sa <- elabTy a
    sb <- elabTy b
    return $ FunTy sa sb 
elabTy (SVarTy n) = do
    ty <- lookupType n
    case ty of
        Nothing -> failFD4 $ "Tipo no declarado: " ++ ppName n
        Just typ -> return typ

typeConverter :: (Name, Ty) -> Ty -> Ty
typeConverter (_, t) tys = FunTy t tys

stypeConverter :: (Name, STy) -> STy -> STy
stypeConverter (_, t) tys = SFunTy t tys
