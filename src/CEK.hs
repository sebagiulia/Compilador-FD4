module CEK where

import Lang
import MonadFD4

data Val =
    Const Const
  | ClosFun Env Name (Sc1 TTerm)  
  | ClosFix Env Name Name (Sc2 TTerm)

data Frame = 
    FArg Env TTerm                 -- p . [] t
  | FFun Val                       -- clos []
  | FIfz Env TTerm TTerm           -- p . ifz [] then t else e
  | FBinaryOpI Env BinaryOp TTerm  -- p . [] + t 
  | FBinaryOpD BinaryOp Val        -- v + []
  | FPrint String                  -- print str []
  | FLet Env Name (Sc1 TTerm)      -- p . let x = [] in t
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
seek (V _ (Bound !n)) e k      = destroy (e!!n) k
seek (V _ (Free nm)) e k        = failFD4 $ "Error de ejecución: variable libre encontrada: " ++ ppName nm
seek (V _ (Global x)) e k      = do
  mtm  <- lookupDecl x  
  case mtm ofx
    Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName nm 
    (Just t) -> seek t e k
seek (Const _ n) e k           = destroy (Const n) k
seek (Lam _ x _ s) e k         = destroy (ClosFun e x s) k
seek (Fix _ f _ x _ s) e k     = destroy (ClosFix e f x s) k
seek (Let _ x _ t s) e k       = seek t e ((FLet e x s):k)


destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy v ((FPrint str):k) = 
  case v of 
    Const n -> do printFD4 (str++show n)
                  return v
    _         -> abort "Error de tipo en runtime! : FPrint"
destroy v ((FBinaryOpI e op t):k) = 
  case v of 
    Const n -> seek t e ((FBinaryOpD op v):k)
    _          -> abort "Error de tipo en runtime! : FBinaryOpI"
destroy v ((FBinaryOpD op (Const m)):k) = 
  case v of 
    Const n -> destroy (Const (semOp op n m)) k
    _       -> abort "Error de tipo en runtime! : FBinaryOpD"
destroy v ((FIfz e t1 t2):k) =
  case v of 
    Const (Cnat 0) -> seek t1 e k
    Const _        -> seek t2 e k
    _              -> abort "Error de tipo en runtime! : FIfz"
destroy v ((FArg e t):k) = 
  case v of
    Const _ -> abort "Error de tipo en runtime! : FArg"
    _       -> seek t e ((FFun v):k) 
destroy v (c:k) =
  case c of 
    ClosFun e x (Sc1 t)   -> seek t (v:e) k 
    ClosFix e f x (Sc2 t) -> seek t (c:v:e) k 
    _                     -> abort "Error de tipo en runtime! : Operación inválida"

{-

  let x = 3 + 1 in 2 + 2  ->  (3 + 1) (2 + 2)
 
||
< let x = t1 in t2,  p         ,                         K > -> 
< t1              ,  p         , p . let x = [] in t2 :  K > ->
<< v1             ,  p         , p . let x = [] in t2 :  K >> -> 
< t2              ,  p(x -> v1),                         K >

-}