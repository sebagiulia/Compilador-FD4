module CEK where

import Lang
import MonadFD4
import Common
import PPrint

data Val =
    VConst Const
  | ClosFun Env Name Ty (Scope (Pos, Ty) Var)  
  | ClosFix Env Name Ty Name Ty (Scope2 (Pos, Ty) Var)
  deriving(Show)

data Frame = 
    FArg Env TTerm                       -- p . [] t
  | FFun Val                             -- clos []
  | FIfz Env TTerm TTerm                 -- p . ifz [] then t else e
  | FBinaryOpI Env BinaryOp TTerm        -- p . [] + t 
  | FBinaryOpD BinaryOp Val              -- v + []
  | FPrint String                        -- print str []
  | FLet Env Name (Scope (Pos, Ty) Var)  -- p . let x = [] in t
  deriving (Show)

type Kont = [Frame]
type Env = [Val]

semOp :: BinaryOp -> Const -> Const -> Const
semOp Add (CNat x) (CNat y) = CNat (x + y)
semOp Sub (CNat x) (CNat y) = CNat (max 0 (x - y))

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek (Print _ str t) e k       = seek t e ((FPrint str):k)
seek (BinaryOp _ op t1 t2) e k = seek t1 e ((FBinaryOpI e op t2):k)
seek (IfZ _ c t1 t2) e k       = seek c e ((FIfz e t1 t2):k)
seek (App _ t1 t2) e k         = seek t1 e ((FArg e t2):k)
seek (V _ (Bound n)) e k       = destroy (e!!n) k
seek (V _ (Free nm)) e k       = failFD4 $ "Error de ejecución: variable libre encontrada: " ++ ppName nm
seek (V _ (Global x)) e k      = do
  mtm  <- lookupDecl x  
  case mtm of
    Nothing  -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName x 
    (Just t) -> seek t e k
seek (Const _ n) e k           = destroy (VConst n) k
seek (Lam _ x t s) e k         = destroy (ClosFun e x t s) k
seek (Fix _ f fty x xty s) e k = destroy (ClosFix e f fty x xty s) k
seek (Let _ x _ t s) e k       = seek t e ((FLet e x s):k)


destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy v ((FPrint str):k) = 
  case v of 
    VConst (CNat n) -> do printLnFD4 (str++show n)
                          destroy v k
    _           -> abort "Error de tipo en runtime! : FPrint"
destroy v ((FBinaryOpI e op t):k) = 
  case v of 
    VConst n -> seek t e ((FBinaryOpD op v):k)
    _           -> abort "Error de tipo en runtime! : FBinaryOpI"
destroy v ((FBinaryOpD op (VConst m)):k) = 
  case v of 
    VConst n -> destroy (VConst (semOp op m n)) k
    _       -> abort "Error de tipo en runtime! : FBinaryOpD"
destroy v ((FIfz e t1 t2):k) =
  case v of 
    VConst (CNat 0) -> seek t1 e k
    VConst _        -> seek t2 e k
    _              -> abort "Error de tipo en runtime! : FIfz"
destroy v ((FArg e t):k) = 
  case v of
    VConst _ -> abort "Error de tipo en runtime! : FArg"
    _       -> seek t e ((FFun v):k) 
destroy v ((FFun c):k) =
  case c of 
    ClosFun e x _ (Sc1 t)     -> seek t (v:e) k 
    ClosFix e f _ x _ (Sc2 t) -> seek t (v:c:e) k 
    _                     -> abort "Error de tipo en runtime! : Operación inválida"
destroy v ((FLet e x (Sc1 t)):k) = seek t (v:e) k 
destroy v (c:k) = abort "Error de tipo en runtime! : Operación inválida"

replaceBound :: Int -> Env -> Var -> Either Val Var
replaceBound pos e (Bound i) = if pos > 0 && pos - i < (length e) then Left (e!!(pos - i)) else Right (Bound i)       
replaceBound _ _ var = Right var
                           
replaceBounds :: Int -> Env -> TTerm -> TTerm
replaceBounds pos _ t@(Const i c)                = t
replaceBounds pos e (Lam i x xty (Sc1 t))        = Lam i x xty (Sc1 (replaceBounds (pos+1) e t))
replaceBounds pos e (App i t1 t2)                = App i (replaceBounds pos e t1) (replaceBounds pos e t2)
replaceBounds pos e (Print i st t)               = Print i st (replaceBounds pos e t)
replaceBounds pos e (BinaryOp i op t1 t2)        = BinaryOp i op (replaceBounds pos e t1) (replaceBounds pos e t2)
replaceBounds pos e (Fix i f fty x xty (Sc2 t2)) = Fix i f fty x xty (Sc2 (replaceBounds (pos+2) e t2))
replaceBounds pos e (IfZ i c t1 t2)              = IfZ i (replaceBounds pos e c) (replaceBounds pos e t1) (replaceBounds pos e t2)
replaceBounds pos e (Let i x ty t1 (Sc1 t2))     = Let i x ty (replaceBounds pos e t1) (Sc1 (replaceBounds (pos+1) e t2))
replaceBounds pos e (V i var) =
  case replaceBound pos e var of
    Right v  -> V i v
    Left val -> val2term i val 

val2term :: (Pos, Ty) -> Val -> TTerm
val2term p (VConst n) = Const p n
val2term p (ClosFun e x xty (Sc1 t)) = let tt = replaceBounds (length e) e t
                                       in Lam p x xty (Sc1 tt) 
val2term p (ClosFix e f fty x xty (Sc2 t)) = let tt = replaceBounds ((length e) + 1) e t 
                                             in Fix p f fty x xty (Sc2 tt) 
