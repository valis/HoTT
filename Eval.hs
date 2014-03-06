module Eval
    ( eval
    , evalOfType
    , typeOf
    ) where

import qualified Data.Map as M

import Parser.AbsGrammar
import Parser.PrintGrammar

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Level = Finite Integer | Omega | Omega1 | Omega2 deriving Eq
type ErrorMsg = String
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi Value (Value -> Value) | Ssigma Value (Value -> Value) -- Constructors for Type_k
    | Snat | Sid Value Value | Stype Level -- Constructors for Type_k
    | Svar String | Sapp Value Value | Srec Value Value Value | Serror [ErrorMsg]
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxT = M.Map String Value

infixr 5 `sarr`, `Spi`
sarr :: Value -> Value -> Value
sarr a b = Spi a (const b)

sprod :: Value -> Value -> Value
sprod a b = Ssigma a (const b)

instance Ord Level where
    compare (Finite x) (Finite y) = compare x y
    compare (Finite _) _ = LT
    compare _ (Finite _) = GT
    compare Omega Omega = EQ
    compare Omega Omega1 = LT
    compare Omega Omega2 = LT
    compare Omega1 Omega1 = EQ
    compare Omega1 Omega2 = LT
    compare Omega2 Omega2 = EQ
    compare _ _ = GT

instance Bounded Level where
    minBound = Finite 0
    maxBound = Omega2

instance Enum Level where
    succ (Finite l) = Finite (succ l)
    succ Omega = Omega1
    succ Omega1 = Omega2
    succ Omega2 = error "Enum.Level.succ: bad argument"
    pred (Finite l) | l > 0= Finite (pred l)
    pred Omega1 = Omega
    pred Omega2 = Omega1
    pred _ = error "Enum.Level.pred: bad argument"
    toEnum = Finite . toInteger
    fromEnum (Finite l) = fromInteger l
    fromEnum _ = error "Enum.Level.fromEnum: bad argument"

checkValue2 :: (Value -> Value -> Value) -> Value -> Value -> Value
checkValue2 f (Serror m1) (Serror m2) = Serror (m1 ++ m2)
checkValue2 f (Serror m) _ = Serror m
checkValue2 f _ (Serror m) = Serror m
checkValue2 f v1 v2 = f v1 v2

maxType :: Value -> Value -> Value
maxType (Stype k1) (Stype k2) = Stype (max k1 k2)
maxType _ _ = Serror ["Expected type"]

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

parseLevel :: String -> Level
parseLevel "Type" = Omega
parseLevel ('T':'y':'p':'e':s) = Finite (read s)

app :: Integer -> Value -> Value -> Value
app n = checkValue2 $ \(Slam _ f) -> f n []

ctxtToCtx :: CtxT -> Ctx
ctxtToCtx = M.mapWithKey (\k v -> (Svar k, v))

ctxToCtxt :: Ctx -> CtxT
ctxToCtxt = M.map snd

renameExpr :: M.Map String v -> String -> Expr -> (String,Expr)
renameExpr m x e = (x', rename e x x')
  where b = M.member x m
        x' = if b then fresh 0 else x
        fv = freeVars e ++ M.keys m
        fresh n | elem y fv = fresh (n + 1)
                | otherwise = y
                where y = x ++ show n

typeOf'nondepType :: CtxT -> Expr -> Expr -> Value
typeOf'nondepType ctx e1 e2 = checkValue2 maxType (typeOf ctx e1) (typeOf ctx e2)

typeOf'depType :: ([TypedVar] -> Expr -> Expr) -> CtxT -> [TypedVar] -> Expr -> Value
typeOf'depType _ ctx [] e = typeOf ctx e
typeOf'depType dt ctx (TypedVar (Var NoArg) t : vars) e = typeOf'nondepType ctx t (dt vars e)
typeOf'depType dt ctx (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e =
    let k1 = typeOf ctx t
        (x',e') = renameExpr ctx x (dt vars e)
        k2 = typeOf (M.insert x' (eval t 0 (ctxtToCtx ctx)) ctx) e'
    in checkValue2 maxType k1 k2
typeOf'depType _ _ (TypedVar _ _ : _) _ = Serror ["Expected identifier"]

typeOf :: CtxT -> Expr -> Value
typeOf _ (Lam _ _) = Serror ["Cannot infer type of lambda expression"]
typeOf ctx (Arr e1 e2) = typeOf'nondepType ctx e1 e2
typeOf ctx (Prod e1 e2) = typeOf'nondepType ctx e1 e2
typeOf ctx (Pi tv e) = typeOf'depType Pi ctx tv e
typeOf ctx (Sigma tv e) = typeOf'depType Sigma ctx tv e
typeOf ctx (Id a b) = checkValue2 cmpTypes (typeOf ctx a) (typeOf ctx b)
  where cmpTypes ta tb = maybe (Serror ["Types differ"]) id (maxTypeValue ta tb)
typeOf _ Nat = Stype (Finite 0)
typeOf _ (Universe (U t)) = Stype $ succ (parseLevel t)
typeOf ctx (App e1 e2) = case typeOf ctx e1 of
    Spi a b -> b $ evalOfType e2 a 0 (ctxtToCtx ctx)
    t -> Serror $ either id (\r -> ["Expected pi type\nActual type: " ++ show r]) $ reify t (Stype maxBound)
typeOf _ (Var NoArg) = Serror ["Expected identifier"]
typeOf ctx (Var (Arg (PIdent (_,x)))) = maybe (Serror ["Unknown identifier " ++ x]) id (M.lookup x ctx)
typeOf _ Suc = sarr Snat Snat
typeOf _ (NatConst x) = Snat
typeOf _ Rec = (Snat `sarr` Stype maxBound) `Spi` \p -> Sapp p Szero `sarr`
    (Snat `Spi` \x -> Sapp p x `sarr` Sapp p (Ssuc x)) `sarr` Snat `Spi` Sapp p
-- Rec : (p : Nat -> Type) -> p 0 -> ((x : Nat) -> p x -> p (Suc x)) -> (x : Nat) -> p x

-- First argument must be well-typed
eval :: Expr -> Integer -> Ctx -> Value
eval (Lam _ _) _ _ = Serror ["Cannot infer type of lambda expression"]
eval (Arr e1 e2) 0 ctx = sarr (eval e1 0 ctx) (eval e2 0 ctx)
eval (Prod e1 e2) 0 ctx = sprod (eval e1 0 ctx) (eval e2 0 ctx)
eval (Pi [] e) n ctx = eval e n ctx
eval (Sigma [] e) n ctx = eval e n ctx
eval (Pi (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Arr t (Pi vars e)) n ctx
eval (Sigma (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Prod t (Sigma vars e)) n ctx
eval (Pi (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval t 0 ctx
  in Spi v1 $ \a -> let (x',e') = renameExpr ctx x (Pi vars e)
                    in eval e' 0 (M.insert x' (a,v1) ctx)
eval (Sigma (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval t 0 ctx
  in Ssigma v1 $ \a -> let (x',e') = renameExpr ctx x (Sigma vars e)
                       in eval e' 0 (M.insert x' (a,v1) ctx)
eval (Pi (TypedVar _ t : vars) e) 0 ctx = Serror ["Expected identifier"]
eval (Sigma (TypedVar _ t : vars) e) 0 ctx = Serror ["Expected identifier"]
eval (Id a b) 0 ctx = Sid (eval a 0 ctx) (eval b 0 ctx)
eval Nat 0 _ = Snat
eval (Universe (U t)) 0 _ = Stype (parseLevel t)
eval (App e1 e2) n ctx = case typeOf (ctxToCtxt ctx) e1 of
    Spi a _ -> app n (eval e1 n ctx) (evalOfType e2 a n ctx)
    t -> Serror ["Expected pi type\nActual type: " ++ show (reify t $ Stype maxBound)]
eval (Var x) n ctx = undefined
eval Suc n ctx = undefined
eval (NatConst x) n ctx = undefined
eval Rec n ctx = undefined

evalOfType :: Expr -> Value -> Integer -> Ctx -> Value
evalOfType (Lam [] e) ty n ctx = evalOfType e ty n ctx
evalOfType (Lam (Binder NoArg:xs) e) (Spi a b) n ctx = Slam "_" $ \k m v ->
    evalOfType (Lam xs e) (b v) k $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType (Lam (Binder (Arg (PIdent (_,x))):xs) e) (Spi a b) n ctx =
    let (x',e') = renameExpr ctx x (Lam xs e)
    in Slam x' $ \k m v -> evalOfType e' (b v) k $ M.insert x' (v,a) $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType (Lam _ _) ty _ _ = case reify ty (Stype maxBound) of
    Left errs -> Serror errs
    Right e -> Serror ["Expected pi type\nActual type: " ++ show e]
evalOfType e ty n ctx = let
    te = reify ty (Stype maxBound)
    te1 = reify (typeOf (ctxToCtxt ctx) e) (Stype maxBound)
    in case (te,te1) of
        (Left errs,_) -> Serror errs
        (_,Left errs) -> Serror errs
        (Right te', Right te1') -> if te1' <= te' then eval e n ctx else
            Serror ["Expected type: " ++ show te' ++ "\nActual type: " ++ show te1']

maxTypeValue :: Value -> Value -> Maybe Value
maxTypeValue = undefined

newtype Norm = Norm Expr

instance Eq Norm where
    Norm e1 == Norm e2 = e1 == e2 -- TODO: alpha conversion?

instance Ord Norm where
    Norm e1 <= Norm e2 = e1 == e2 -- TODO: Define it

instance Show Norm where
    show (Norm e) = printTree e

reify :: Value -> Value -> Either [ErrorMsg] Norm
reify = undefined

freeVars :: Expr -> [String]
freeVars = undefined

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename _ _ _ = undefined
