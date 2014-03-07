module Eval
    ( eval
    , evalOfType
    , typeOf
    , hasType
    , reify
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Control.Monad

import Parser.AbsGrammar
import Parser.PrintGrammar

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Level = Finite Integer | Omega | Omega1 | Omega2 deriving Eq
type ErrorMsg = String
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi String Value (Value -> Value) | Ssigma String Value (Value -> Value) -- Constructors for Type_k
    | Snat | Sid Value Value Value | Stype Level -- Constructors for Type_k
    | Sidp Value -- Constructor for Id
    | Ne Norm
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxT = M.Map String Value

snorm :: Expr -> Value
snorm = Ne . Norm

svar :: String -> Value
svar x = snorm $ Var $ Arg $ PIdent ((0,0),x)

infixl 5 $$
($$) = App

infixr 5 `sarr`
sarr :: Value -> Value -> Value
sarr a b = Spi "_" a (const b)

sprod :: Value -> Value -> Value
sprod a b = Ssigma "_" a (const b)

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

idp :: Value -> Value
idp = action [Ud]

pmap :: Integer -> Value -> Value -> Value
pmap n f = app (n + 1) (idp f)

unBinder :: Binder -> String
unBinder (Binder NoArg) = "_"
unBinder (Binder (Arg (PIdent (_,x)))) = x

parseLevel :: String -> Level
parseLevel "Type" = Omega
parseLevel ('T':'y':'p':'e':s) = Finite (read s)

ctxtToCtx :: CtxT -> Ctx
ctxtToCtx = M.mapWithKey $ \k v -> (liftValue [k] (svar k) v, v)

ctxToCtxt :: Ctx -> CtxT
ctxToCtxt = M.map snd

freshName :: String -> [String] -> String
freshName "_" vars = freshName "x" vars
freshName base vars | elem base vars = go 0
                    | otherwise = base
  where
    go n | elem x vars = go (n + 1)
         | otherwise = x
         where x = base ++ show n

renameExpr :: [String] -> String -> Expr -> (String,Expr)
renameExpr m x e = let x' = freshName x (freeVars e ++ m) in (x', rename e x x')

freeVars :: Expr -> [String]
freeVars (Lam bnds e) = freeVars e \\ map unBinder bnds
freeVars (Arr e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pi [] e) = freeVars e
freeVars (Pi (TypedVar (Var NoArg) t : xs) e) = freeVars t `union` freeVars (Pi xs e)
freeVars (Pi (TypedVar (Var (Arg (PIdent (_,x)))) t : xs) e) = freeVars t `union` delete x (freeVars $ Pi xs e)
freeVars (Prod e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Sigma [] e) = freeVars e
freeVars (Sigma (TypedVar (Var NoArg) t : xs) e) = freeVars t `union` freeVars (Sigma xs e)
freeVars (Sigma (TypedVar (Var (Arg (PIdent (_,x)))) t : xs) e) = freeVars t `union` delete x (freeVars $ Sigma xs e)
freeVars (Id e1 e2) = freeVars e1 `union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var (Arg (PIdent (_,x)))) = [x]
freeVars (Var NoArg) = []
freeVars Nat = []
freeVars Suc = []
freeVars Rec = []
freeVars Idp = []
freeVars (Pmap e) = freeVars e
freeVars (NatConst _) = []
freeVars (Universe _) = []

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename e@(Lam bs _) x y | elem x (map unBinder bs) = e
rename (Lam bs e) x y = Lam bs (rename e x y)
rename (Arr e1 e2) x y = Arr (rename e1 x y) (rename e2 x y)
rename (Pi [] e) x y = rename e x y
rename (Pi (TypedVar (Var (Arg (PIdent (i,z)))) t : bs) e) x y | x == z
    = Pi [TypedVar (Var (Arg (PIdent (i,z)))) (rename t x y)] (Pi bs e)
rename (Pi (TypedVar v t : bs) e) x y = Pi [TypedVar v (rename t x y)] $ rename (Pi bs e) x y
rename (Prod e1 e2) x y = Prod (rename e1 x y) (rename e2 x y)
rename (Sigma [] e) x y = rename e x y
rename (Sigma (TypedVar (Var (Arg (PIdent (i,z)))) t : bs) e) x y | x == z
    = Sigma [TypedVar (Var (Arg (PIdent (i,z)))) (rename t x y)] (Sigma bs e)
rename (Sigma (TypedVar v t : bs) e) x y = Sigma [TypedVar v (rename t x y)] $ rename (Sigma bs e) x y
rename (Id e1 e2) x y = Id (rename e1 x y) (rename e2 x y)
rename (App e1 e2) x y = App (rename e1 x y) (rename e2 x y)
rename (Var (Arg (PIdent (i,z)))) x y | x == z = Var $ Arg $ PIdent (i,y)
rename e@(Var _) _ _ = e
rename Nat _ _ = Nat
rename Suc _ _ = Suc
rename Rec _ _ = Rec
rename Idp _ _ = Idp
rename (Pmap e) x y = Pmap (rename e x y)
rename e@(NatConst _) _ _ = e
rename e@(Universe _) _ _ = e

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
        (x',e') = renameExpr (M.keys ctx) x (dt vars e)
        k2 = typeOf (M.insert x' (eval t 0 (ctxtToCtx ctx)) ctx) e'
    in liftErr2 maxType k1 k2
typeOf'depType _ _ (TypedVar _ _ : _) _ = Left ["Expected identifier"]

typeOf :: CtxT -> Expr -> Err Value
typeOf ctx (Lam [] e) = typeOf ctx e
typeOf _ (Lam _ _) = Left ["Cannot infer type of lambda expression"]
typeOf _ Idp = Left ["Cannot infer type of idp"]
typeOf _ (Pmap _) = Left ["Cannot infer type of pmap"]
typeOf ctx (App Idp e) = do
    t <- typeOf ctx e
    let v = eval e 0 (ctxtToCtx ctx)
    Right (Sid t v v)
typeOf ctx (App (Pmap e1) e2) = do
    t2 <- typeOf ctx e2
    case t2 of
        Sid t a b -> do
            s <- typeOfLam ctx e1 t2
            let e' = app 0 $ evalOfType e1 (sarr t s) 0 (ctxtToCtx ctx)
            Right $ Sid s (e' a) (e' b)
        _ -> Left ["Expected Id type\nActual type: " ++ show (reify (M.keys ctx) t2 $ Stype maxBound)]
typeOf ctx (Arr e1 e2) = typeOf'nondepType ctx e1 e2
typeOf ctx (Prod e1 e2) = typeOf'nondepType ctx e1 e2
typeOf ctx (Pi tv e) = typeOf'depType Pi ctx tv e
typeOf ctx (Sigma tv e) = typeOf'depType Sigma ctx tv e
typeOf ctx (Id a b) = do
    a' <- typeOf ctx a
    b' <- typeOf ctx b
    case cmpTypes (M.keys ctx) a' b' of
        Just o | o == EQ -> typeOf ctx $ unNorm $ reify (M.keys ctx) a' (Stype maxBound)
        _ -> Left ["Types differ"]
typeOf _ Nat = Right $ Stype (Finite 0)
typeOf _ (Universe (U t)) = Right $ Stype $ succ (parseLevel t)
typeOf ctx (App e1 e2) = do
    t <- typeOf ctx e1
    case t of
        Spi _ a b -> hasType ctx e2 a >> Right (b $ evalOfType e2 a 0 $ ctxtToCtx ctx)
        _ -> Left ["Expected pi type\nActual type: " ++ show (reify (M.keys ctx) t $ Stype maxBound)]
typeOf _ (Var NoArg) = Left ["Expected identifier"]
typeOf ctx (Var (Arg (PIdent (_,x)))) = maybe (Left ["Unknown identifier " ++ x]) Right (M.lookup x ctx)
typeOf _ Suc = Right (sarr Snat Snat)
typeOf _ (NatConst x) = Right Snat
typeOf _ Rec = Right $ Spi "P" (Snat `sarr` Stype maxBound) $ \p -> app 0 p Szero `sarr`
    (Spi "x" Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x

typeOfLam :: CtxT -> Expr -> Value -> Err Value
typeOfLam ctx (Lam [] e) t = typeOfLam ctx e t
typeOfLam ctx (Lam (x:xs) e) t =
    let (x',e') = renameExpr (M.keys ctx) (unBinder x) (Lam xs e)
    in do
        s <- typeOf (M.insert x' t ctx) e'
        if elem x' $ freeVars $ unNorm $ reify (x' : M.keys ctx) s (Stype maxBound)
            then Left ["Cannot infer type of lambda expression"]
            else Right s
typeOfLam ctx e ty = do
    t <- typeOf ctx e
    case t of
        Spi x a b -> do
            when (cmpTypes (M.keys ctx) a ty /= Just EQ) $
                Left ["Expected type: " ++ show (reify (M.keys ctx) a  $ Stype maxBound) ++
                      "\nActual type: " ++ show (reify (M.keys ctx) ty $ Stype maxBound)]
            let x' = freshName x (M.keys ctx)
                b' = b $ liftValue [x'] (svar x') a
            if elem x' $ freeVars $ unNorm $ reify (x' : M.keys ctx) b' (Stype maxBound)
                then Left ["Expected arrow type\nActual type: " ++ show (reify (M.keys ctx) (Spi x a b) $ Stype maxBound)]
                else Right b'
        _ -> Left ["Expected pi type\nActual type: " ++ show (reify (M.keys ctx) t $ Stype maxBound)]

hasType :: CtxT -> Expr -> Value -> Err ()
hasType ctx (Lam [] e) ty = hasType ctx e ty
hasType ctx (Lam (x:xs) e) (Spi z a b) =
    let (x',e') = renameExpr (M.keys ctx) (unBinder x) (Lam xs e)
    in hasType (M.insert x' a ctx) e' (b $ liftValue [x'] (svar x') a)
hasType ctx (Lam _ _) ty = Left ["Expected pi type\nActual type: " ++ show (reify (M.keys ctx) ty $ Stype maxBound)]
hasType ctx Idp (Spi x a b) =
    let x' = freshName x (M.keys ctx)
        x'' = liftValue [x'] (svar x') a
    in case b x'' of
        Sid t l r | cmpTypes (x' : M.keys ctx) a t == Just EQ -> do
            cmpValues (x' : M.keys ctx) l x'' t
            cmpValues (x' : M.keys ctx) r x'' t
        t -> Left ["Expected Id " ++ show (reify (x' : M.keys ctx) a $ Stype maxBound) ++ " " ++ x' ++ " " ++ x' ++
                "\nActual type: " ++ show (reify (x' : M.keys ctx) t $ Stype maxBound)]
hasType ctx Idp ty = Left ["Expected pi type\nActual type: " ++ show (reify (M.keys ctx) ty $ Stype maxBound)]
hasType ctx (Pmap e) (Spi x a@(Sid t l r) b) =
    let x' = freshName x (M.keys ctx)
    in case b (liftValue [x'] (svar x') a) of
        Sid s l' r' -> do
            hasType ctx e (sarr t s)
            let e' = evalOfType e (sarr t s) 0 (ctxtToCtx ctx)
            cmpValues (x' : M.keys ctx) l' (app 0 e' l) s
            cmpValues (x' : M.keys ctx) r' (app 0 e' r) s
        b' -> Left ["Expected Id type\nActual type: " ++ show (reify (M.keys ctx) b' $ Stype maxBound)]
hasType ctx (Pmap _) (Spi x a _) = Left ["Expected Id type\nActual type: " ++ show (reify (M.keys ctx) a $ Stype maxBound)]
hasType ctx (Pmap _) ty = Left ["Expected pi type\nActual type: " ++ show (reify (M.keys ctx) ty $ Stype maxBound)]
hasType ctx e ty = do
    ty1 <- typeOf ctx e
    case cmpTypes (M.keys ctx) ty1 ty of
        Just o | o /= GT -> Right ()
        _ -> Left ["Expected type: " ++ show (reify (M.keys ctx) ty  $ Stype maxBound) ++ "\n" ++
                    "Actual type: "   ++ show (reify (M.keys ctx) ty1 $ Stype maxBound)]

eval :: Expr -> Integer -> Ctx -> Value
eval (App Idp e) n ctx = eval e (n + 1) (M.map (\(v,t) -> (idp v,t)) ctx)
eval (App (Pmap e1) e2) n ctx = pmap n (eval e1 n ctx) (eval e2 n ctx)
eval (Arr e1 e2) 0 ctx = sarr (eval e1 0 ctx) (eval e2 0 ctx)
eval (Prod e1 e2) 0 ctx = sprod (eval e1 0 ctx) (eval e2 0 ctx)
eval (Pi [] e) n ctx = eval e n ctx
eval (Sigma [] e) n ctx = eval e n ctx
eval (Pi (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Arr t (Pi vars e)) n ctx
eval (Sigma (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Prod t (Sigma vars e)) n ctx
eval (Pi (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval t 0 ctx
      (x',e') = renameExpr (M.keys ctx) x (Pi vars e)
  in Spi x' v1 $ \a -> eval e' 0 (M.insert x' (a,v1) ctx)
eval (Sigma (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval t 0 ctx
      (x',e') = renameExpr (M.keys ctx) x (Sigma vars e)
  in Ssigma x' v1 $ \a -> eval e' 0 (M.insert x' (a,v1) ctx)
eval (Id a b) 0 ctx = Sid (either (const internalError) id $ typeOf (ctxToCtxt ctx) a) (eval a 0 ctx) (eval b 0 ctx)
eval Nat 0 _ = Snat
eval (Universe (U t)) 0 _ = Stype (parseLevel t)
eval (App e1 e2) n ctx = 
    let Right (Spi _ a _) = typeOf (ctxToCtxt ctx) e1
    in app n (eval e1 n ctx) (evalOfType e2 a n ctx)
eval (Var (Arg (PIdent (_,x)))) _ ctx = fst $ fromJust (M.lookup x ctx)
eval Suc _ _ = Slam "n" $ \_ _ -> Ssuc
eval (NatConst x) _ _ = genConst x
  where genConst 0 = Szero
        genConst n = Ssuc $ genConst (n - 1)
eval Rec _ ctx = Slam "P" $ \pk pm pv -> Slam "z" $ \zk zm zv -> Slam "s" $ \sk sm sv -> Slam "x" $ \xk xm ->
    rec ctx xk (action xm $ action sm $ action zm pv) (action xm $ action sm zv) (action xm sv)

evalOfType :: Expr -> Value -> Integer -> Ctx -> Value
evalOfType (Lam [] e) ty n ctx = evalOfType e ty n ctx
evalOfType (Lam (Binder NoArg:xs) e) (Spi _ a b) n ctx = Slam "_" $ \k m v ->
    evalOfType (Lam xs e) (b v) k $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType (Lam (Binder (Arg (PIdent (_,x))):xs) e) (Spi _ a b) n ctx =
    let (x',e') = renameExpr (M.keys ctx) x (Lam xs e)
    in Slam x' $ \k m v -> evalOfType e' (b v) k $ M.insert x' (v,a) $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType Idp t@(Spi x _ _) n ctx =
    let x' = Arg $ PIdent ((-1,-1), if x == "_" then "x" else x)
    in evalOfType (Lam [Binder x'] $ App Idp $ Var x') t n ctx
evalOfType (Pmap e) t@(Spi x _ _) n ctx =
    let x' = Arg $ PIdent ((-1,-1), freshName x $ freeVars e)
    in evalOfType (Lam [Binder x'] $ App (Pmap e) $ Var x') t n ctx
evalOfType e _ n ctx = eval e n ctx

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) = f n []

rec :: Ctx -> Integer -> Value -> Value -> Value -> Value -> Value
rec ctx n p z s = go
  where
    go Szero = z
    go (Ssuc x) = app n s $ app n x (go x)
    go t@(Ne (Norm e)) =
        let r = Rec $$ unNorm (reify (M.keys ctx) p $ Snat `sarr` Stype maxBound)
                    $$ unNorm (reify (M.keys ctx) z $ app n p Szero)
                    $$ unNorm (reify (M.keys ctx) s $ Spi "x" Snat $ \x -> app n p x `sarr` app n p (Ssuc x))
                    $$ e
        in liftValue (freeVars r) (snorm r) (app n p t)

cmpTypes :: [String] -> Value -> Value -> Maybe Ordering
cmpTypes ctx (Spi x a b) (Spi _ a' b') = case (cmpTypes ctx a' a, cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName x ctx
          ctx' = fresh:ctx
cmpTypes ctx (Ssigma x a b) (Ssigma _ a' b') = case (cmpTypes ctx a a', cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName x ctx
          ctx' = fresh:ctx
cmpTypes ctx (Sid _ a b) (Sid _ a' b') = case (cmpTypes ctx a a', cmpTypes ctx b b') of
    (Just EQ, Just EQ) -> Just EQ
    _ -> Nothing
cmpTypes _ Snat Snat = Just EQ
cmpTypes _ (Stype k) (Stype k') = Just (compare k k')
cmpTypes _ (Ne t) (Ne t') = if t == t' then Just EQ else Nothing
cmpTypes _ _ _ = Nothing

cmpValues :: [String] -> Value -> Value -> Value -> Err ()
cmpValues ctx e1 e2 t =
    let e1' = reify ctx e1 t
        e2' = reify ctx e2 t
    in if e1' == e2' then Right () else Left ["Expected term: " ++ show e1' ++ "\nActual term: " ++ show e2']

newtype Norm = Norm { unNorm :: Expr }

instance Eq Norm where
    Norm e1 == Norm e2 = e1 == e2 -- TODO: alpha conversion?

instance Show Norm where
    show (Norm e) = printTree e

liftValue :: [String] -> Value -> Value -> Value
liftValue _ e@(Slam _ _) (Spi _ _ _) = e
liftValue fv e (Spi x a b) =
    let x' = freshName x fv
    in Slam x' $ \k m -> app k (action m e)
liftValue _ t _ = t

reify :: [String] -> Value -> Value -> Norm
reify ctx (Slam x f) (Spi _ a b) =
    let x' = freshName x ctx
        bnd = [Binder $ Arg $ PIdent ((0,0),x')]
    in Norm $ Lam bnd $ unNorm $ reify (x':ctx) (f 0 [] $ liftValue [x'] (svar x') a) $ b (svar x')
reify _ Szero Snat = Norm (NatConst 0)
reify ctx (Ssuc e) Snat = let Norm (NatConst n) = reify ctx e Snat in Norm $ NatConst $ n + 1
reify ctx (Spi x a b) (Stype l) =
    let x' = freshName x ctx
        bnd = [TypedVar (Var $ Arg $ PIdent ((0,0),x')) $ unNorm $ reify ctx a $ Stype l]
    in Norm $ Pi bnd $ unNorm $ reify (x':ctx) (b $ svar x') (Stype l)
reify ctx (Ssigma x a b) (Stype l) =
    let x' = freshName x ctx
        bnd = [TypedVar (Var $ Arg $ PIdent ((0,0),x')) $ unNorm $ reify ctx a $ Stype l]
    in Norm $ Sigma bnd $ unNorm $ reify (x':ctx) (b $ svar x') (Stype l)
reify ctx (Sid t a b) (Stype _) = Norm $ Id (unNorm $ reify ctx a t) (unNorm $ reify ctx b t)
reify _ (Stype (Finite k)) (Stype _) = Norm $ Universe $ U ("Type" ++ show k)
reify _ (Stype Omega) (Stype _) = Norm $ Universe (U "Type")
reify _ (Stype Omega1) (Stype _) = Norm $ Universe (U "TYPE")
reify _ Snat (Stype _) = Norm Nat
reify _ (Ne e) _ = e

internalError :: a
internalError = error "INTERNAL_ERROR"
