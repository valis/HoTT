module Eval
    ( eval
    , evalOfType
    , typeOf
    , hasType
    ) where

import qualified Data.Map as M
import Data.Maybe

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
    | Ne Norm
    -- | Svar String | Sapp Value Value | Srec Value Value Value | Serror [ErrorMsg]
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxT = M.Map String Value

snorm :: Expr -> Value
snorm = Ne . Norm

svar :: String -> Value
svar x = snorm $ Var $ Arg $ PIdent ((0,0),x)

infixl 5 $$
($$) = App

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

type Err a = Either [ErrorMsg] a

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

parseLevel :: String -> Level
parseLevel "Type" = Omega
parseLevel ('T':'y':'p':'e':s) = Finite (read s)

ctxtToCtx :: CtxT -> Ctx
ctxtToCtx = M.mapWithKey $ \k v -> (liftValue (svar k) v, v)

ctxToCtxt :: Ctx -> CtxT
ctxToCtxt = M.map snd

freshName :: String -> [String] -> String
freshName base vars = go 0
  where go n | elem x vars = go (n + 1)
             | otherwise = x
             where x = base ++ show n

renameExpr :: M.Map String v -> String -> Expr -> (String,Expr)
renameExpr m x e | M.member x m = (x', rename e x x')
                 | otherwise = (x,e)
                 where x' = freshName x (freeVars e ++ M.keys m)

liftErr2 :: (a -> b -> Err c) -> Err a -> Err b -> Err c
liftErr2 f (Left m1) (Left m2) = Left (m1 ++ m2)
liftErr2 f (Left m) _ = Left m
liftErr2 f _ (Left m) = Left m
liftErr2 f (Right v1) (Right v2) = f v1 v2

maxType :: Value -> Value -> Err Value
maxType (Stype k1) (Stype k2) = Right $ Stype (max k1 k2)
maxType _ _ = Left ["Expected type"]

typeOf'nondepType :: CtxT -> Expr -> Expr -> Err Value
typeOf'nondepType ctx e1 e2 = liftErr2 maxType (typeOf ctx e1) (typeOf ctx e2)

typeOf'depType :: ([TypedVar] -> Expr -> Expr) -> CtxT -> [TypedVar] -> Expr -> Err Value
typeOf'depType _ ctx [] e = typeOf ctx e
typeOf'depType dt ctx (TypedVar (Var NoArg) t : vars) e = typeOf'nondepType ctx t (dt vars e)
typeOf'depType dt ctx (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e =
    let k1 = typeOf ctx t
        (x',e') = renameExpr ctx x (dt vars e)
        k2 = typeOf (M.insert x' (eval t 0 (ctxtToCtx ctx)) ctx) e'
    in liftErr2 maxType k1 k2
typeOf'depType _ _ (TypedVar _ _ : _) _ = Left ["Expected identifier"]

typeOf :: CtxT -> Expr -> Err Value
typeOf _ (Lam _ _) = Left ["Cannot infer type of lambda expression"]
typeOf ctx (Arr e1 e2) = typeOf'nondepType ctx e1 e2
typeOf ctx (Prod e1 e2) = typeOf'nondepType ctx e1 e2
typeOf ctx (Pi tv e) = typeOf'depType Pi ctx tv e
typeOf ctx (Sigma tv e) = typeOf'depType Sigma ctx tv e
typeOf ctx (Id a b) = do
    a' <- typeOf ctx a
    b' <- typeOf ctx b
    case cmpTypes (M.keys ctx) a' b' of
        Just o | o == EQ -> {- typeOfType ctx a' -} undefined
        _ -> Left ["Types differ"]
typeOf _ Nat = Right $ Stype (Finite 0)
typeOf _ (Universe (U t)) = Right $ Stype $ succ (parseLevel t)
typeOf ctx (App e1 e2) = typeOf ctx e1 >>= \t -> case t of
    Spi a b -> hasType ctx e2 a >> Right (b $ evalOfType e2 a 0 $ ctxtToCtx ctx)
    _ -> Left ["Expected pi type\nActual type: " ++ show (reify t $ Stype maxBound)]
typeOf _ (Var NoArg) = Left ["Expected identifier"]
typeOf ctx (Var (Arg (PIdent (_,x)))) = maybe (Left ["Unknown identifier " ++ x]) Right (M.lookup x ctx)
typeOf _ Suc = Right (sarr Snat Snat)
typeOf _ (NatConst x) = Right Snat
typeOf _ Rec = Right $ (Snat `sarr` Stype maxBound) `Spi` \p -> app 0 p Szero `sarr`
    (Snat `Spi` \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Snat `Spi` app 0 p
-- Rec : (p : Nat -> Type) -> p 0 -> ((x : Nat) -> p x -> p (Suc x)) -> (x : Nat) -> p x

hasType :: CtxT -> Expr -> Value -> Err ()
hasType ctx (Lam [] e) ty = hasType ctx e ty
hasType ctx (Lam (Binder arg:xs) e) (Spi a b) =
    let x = case arg of { NoArg -> "x"; Arg (PIdent (_,y)) -> y }
        (x',e') = renameExpr ctx x (Lam xs e)
    in hasType (M.insert x' a ctx) e' (b $ liftValue (svar x') a)
hasType _ (Lam _ _) ty = Left ["Expected pi type\nActual type: " ++ show (reify ty $ Stype maxBound)]
hasType ctx e ty = do
    ty1 <- typeOf ctx e
    case cmpTypes (M.keys ctx) ty1 ty of
        Just o | o /= GT -> Right ()
        _ -> Left ["Expected type: " ++ show (reify ty  $ Stype maxBound) ++ "\n" ++
                    "Actual type: "   ++ show (reify ty1 $ Stype maxBound)]

eval :: Expr -> Integer -> Ctx -> Value
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
eval (Id a b) 0 ctx = Sid (eval a 0 ctx) (eval b 0 ctx)
eval Nat 0 _ = Snat
eval (Universe (U t)) 0 _ = Stype (parseLevel t)
eval (App e1 e2) n ctx = 
    let Right (Spi a _) = typeOf (ctxToCtxt ctx) e1
    in app n (eval e1 n ctx) (evalOfType e2 a n ctx)
eval (Var (Arg (PIdent (_,x)))) _ ctx = fst $ fromJust (M.lookup x ctx)
eval Suc _ _ = Slam "n" $ \_ _ -> Ssuc
eval (NatConst x) _ _ = genConst x
  where genConst 0 = Szero
        genConst n = Ssuc $ genConst (n - 1)
eval Rec _ _ = Slam "P" $ \pk pm pv -> Slam "z" $ \zk zm zv -> Slam "s" $ \sk sm sv -> Slam "x" $ \xk xm ->
    rec xk (action xm $ action sm $ action zm pv) (action xm $ action sm zv) (action xm sv)

evalOfType :: Expr -> Value -> Integer -> Ctx -> Value
evalOfType (Lam [] e) ty n ctx = evalOfType e ty n ctx
evalOfType (Lam (Binder NoArg:xs) e) (Spi a b) n ctx = Slam "_" $ \k m v ->
    evalOfType (Lam xs e) (b v) k $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType (Lam (Binder (Arg (PIdent (_,x))):xs) e) (Spi a b) n ctx =
    let (x',e') = renameExpr ctx x (Lam xs e)
    in Slam x' $ \k m v -> evalOfType e' (b v) k $ M.insert x' (v,a) $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType e _ n ctx = eval e n ctx

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) = f n []

rec :: Integer -> Value -> Value -> Value -> Value -> Value
rec n p z s = go
  where
    go Szero = z
    go (Ssuc x) = app n s $ app n x (go x)
    go t@(Ne (Norm e)) = liftValue (app n p t) $ snorm $ Rec $$ unNorm (reify p $ Snat `sarr` Stype maxBound) $$
        unNorm (reify z $ app n p Szero) $$ unNorm (reify s $ Snat `Spi` \x -> app n p x `sarr` app n p (Ssuc x)) $$ e

cmpTypes :: [String] -> Value -> Value -> Maybe Ordering
cmpTypes ctx (Spi a b) (Spi a' b') = case (cmpTypes ctx a' a, cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName "x" ctx
          ctx' = fresh:ctx
cmpTypes ctx (Ssigma a b) (Ssigma a' b') = case (cmpTypes ctx a a', cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName "x" ctx
          ctx' = fresh:ctx
cmpTypes ctx (Sid a b) (Sid a' b') = case (cmpTypes ctx a a', cmpTypes ctx b b') of
    (Just EQ, Just EQ) -> Just EQ
    _ -> Nothing
cmpTypes _ Snat Snat = Just EQ
cmpTypes _ (Stype k) (Stype k') = Just (compare k k')
cmpTypes _ (Ne t) (Ne t') = if t == t' then Just EQ else Nothing
cmpTypes _ _ _ = Nothing

newtype Norm = Norm { unNorm :: Expr }

instance Eq Norm where
    Norm e1 == Norm e2 = e1 == e2 -- TODO: alpha conversion?

instance Show Norm where
    show (Norm e) = printTree e

liftValue :: Value -> Value -> Value
liftValue = undefined

reify :: Value -> Value -> Norm
reify = undefined

freeVars :: Expr -> [String]
freeVars = undefined

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename _ _ _ = undefined

internalError :: a
internalError = error "INTERNAL_ERROR"
