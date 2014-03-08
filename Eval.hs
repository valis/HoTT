module Eval
    ( eval
    , evalOfType
    , typeOf
    , hasType
    , reify
    , Value(..)
    , Norm(..)
    , unBinder
    , Ctx
    , CtxT
    , processDefs
    , evalDecl
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.State

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
    pred (Finite l) | l > 0 = Finite (pred l)
    pred Omega1 = Omega
    pred Omega2 = Omega1
    pred _ = error "Enum.Level.pred: bad argument"
    toEnum = Finite . toInteger
    fromEnum (Finite l) = fromInteger l
    fromEnum _ = error "Enum.Level.fromEnum: bad argument"

type Err a = Either [ErrorMsg] a

processDefs :: [Def] -> Err [(String,Maybe Expr,[Arg],Expr)]
processDefs defs =
    let typeSigs = filterTypeSigs defs
        funDecls = filterFunDecls defs
        typeSigsDup = duplicates (map fst typeSigs)
        funDeclsDup = duplicates (map fst funDecls)
    in if not (null typeSigsDup) || not (null funDeclsDup)
        then Left $ map (\name -> "Duplicate type signatures for " ++ name) typeSigsDup
                 ++ map (\name -> "Multiple declarations of " ++ name) funDeclsDup
        else Right $ map (\(name,(args,expr)) -> (name,lookup name typeSigs,args,expr)) funDecls
  where
    filterTypeSigs :: [Def] -> [(String,Expr)]
    filterTypeSigs [] = []
    filterTypeSigs (DefType (PIdent (_,x)) e : defs) = (x,e) : filterTypeSigs defs
    filterTypeSigs (_:defs) = filterTypeSigs defs
    
    filterFunDecls :: [Def] -> [(String,([Arg],Expr))]
    filterFunDecls [] = []
    filterFunDecls (Def (PIdent (_,x)) a e : defs) = (x,(a,e)) : filterFunDecls defs
    filterFunDecls (_:defs) = filterFunDecls defs
    
    duplicates :: [String] -> [String]
    duplicates [] = []
    duplicates (x:xs) = case findRemove xs of
        Nothing -> duplicates xs
        Just xs' -> x : duplicates xs'
      where
        findRemove :: [String] -> Maybe [String]
        findRemove [] = Nothing
        findRemove (y:ys) | x == y = Just $ maybe ys id (findRemove ys)
                          | otherwise = fmap (y:) (findRemove ys)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

idp :: Value -> Value
idp = action [Ud]

pmap :: Integer -> Value -> Value -> Value
pmap n f = app (n + 1) (idp f)

unArg :: Arg -> String
unArg NoArg = "_"
unArg (Arg (PIdent (_,x))) = x

unBinder :: Binder -> String
unBinder (Binder b) = unArg b

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

freeVarsDef :: [Def] -> Expr -> [String]
freeVarsDef [] e = freeVars e
freeVarsDef (DefType _ t : ds) e = freeVars t `union` freeVarsDef ds e
freeVarsDef (Def (PIdent (_,x)) as t : ds) e = (freeVars t \\ map unArg as) `union` delete x (freeVarsDef ds e)

freeVars :: Expr -> [String]
freeVars (Let defs e) = freeVarsDef defs e
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

renameDefs :: [Def] -> Expr -> String -> String -> ([Def],Expr)
renameDefs [] e x y = ([], rename e x y)
renameDefs r@(DefType (PIdent (i,z)) t : defs) e x y
    | z == x = (r,e)
    | z == y =
        let (y', Let defs1 e1) = renameExpr [z,x] y (Let defs e)
            (defs2, e2) = renameDefs defs1 e1 x y
        in (DefType (PIdent (i,y')) (rename t x y) : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
        in (DefType (PIdent (i,z)) (rename t x y) : defs', e')
renameDefs r@(Def (PIdent (i,z)) as t : defs) e x y
    | z == x = (r,e)
    | z == y =
        let (y', Let defs1 e1) = renameExpr [z,x] y (Let defs e)
            (defs2, e2) = renameDefs defs1 e1 x y
            Lam as' t' = rename (Lam (map Binder as) t) x y
        in (Def (PIdent (i,y')) (map (\(Binder a) -> a) as') t' : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
            Lam as' t' = rename (Lam (map Binder as) t) x y
        in (Def (PIdent (i,z)) (map (\(Binder a) -> a) as') t' : defs', e')

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename (Let defs e) x y = let (defs',e') = renameDefs defs e x y in Let defs' e'
rename e@(Lam bs e1) x y
    | elem x bs' = e
    | elem y bs' = Lam (map (\y1 -> if unBinder y1 == y then renameBinder y1 y' else y1) bs) (rename e' x y)
    | otherwise = Lam bs (rename e1 x y)
  where bs' = map unBinder bs
        (y',e') = renameExpr (x:bs') y e1
        renameBinder :: Binder -> String -> Binder
        renameBinder (Binder NoArg) _ = Binder NoArg
        renameBinder (Binder (Arg (PIdent (i,_)))) x = Binder $ Arg $ PIdent (i,x)
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

typeOf'nondepType :: Ctx -> CtxT -> Expr -> Expr -> Err Value
typeOf'nondepType gctx ctx e1 e2 = liftErr2 maxType (typeOf gctx ctx e1) (typeOf gctx ctx e2)

typeOf'depType :: Ctx -> ([TypedVar] -> Expr -> Expr) -> CtxT -> [TypedVar] -> Expr -> Err Value
typeOf'depType gctx _ ctx [] e = typeOf gctx ctx e
typeOf'depType gctx dt ctx (TypedVar (Var NoArg) t : vars) e = typeOf'nondepType gctx ctx t (dt vars e)
typeOf'depType gctx dt ctx (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e =
    let k1 = typeOf gctx ctx t
        (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (dt vars e)
        k2 = typeOf gctx (M.insert x' (eval gctx t 0 (ctxtToCtx ctx)) ctx) e'
    in liftErr2 maxType k1 k2
typeOf'depType _ _ _ (TypedVar _ _ : _) _ = Left ["Expected identifier"]

typeOf :: Ctx -> CtxT -> Expr -> Err Value
typeOf gctx ctx (Lam [] e) = typeOf gctx ctx e
typeOf _ _ (Lam _ _) = Left ["Cannot infer type of lambda expression"]
typeOf _ _ Idp = Left ["Cannot infer type of idp"]
typeOf _ _ (Pmap _) = Left ["Cannot infer type of pmap"]
typeOf gctx ctx (Let defs e) = do
    decls <- processDefs defs
    let st = forM_ decls $ \(name,ty,args,expr) -> evalDecl name (Lam (map Binder args) expr) ty
    (gctx',ctx') <- execStateT st (gctx, ctxtToCtx ctx)
    typeOf gctx' (ctxToCtxt ctx') e
typeOf gctx ctx (App Idp e) = do
    t <- typeOf gctx ctx e
    let v = eval gctx e 0 (ctxtToCtx ctx)
    Right (Sid t v v)
typeOf gctx ctx (App (Pmap e1) e2) = do
    t2 <- typeOf gctx ctx e2
    case t2 of
        Sid t a b -> do
            s <- typeOfLam gctx ctx e1 t2
            let e' = app 0 $ evalOfType gctx e1 (sarr t s) 0 (ctxtToCtx ctx)
            Right $ Sid s (e' a) (e' b)
        _ -> Left ["Expected Id type\nActual type: " ++ show (reify (M.keys gctx ++ M.keys ctx) t2 $ Stype maxBound)]
typeOf gctx ctx (Arr e1 e2) = typeOf'nondepType gctx ctx e1 e2
typeOf gctx ctx (Prod e1 e2) = typeOf'nondepType gctx ctx e1 e2
typeOf gctx ctx (Pi tv e) = typeOf'depType gctx Pi ctx tv e
typeOf gctx ctx (Sigma tv e) = typeOf'depType gctx Sigma ctx tv e
typeOf gctx ctx (Id a b) = do
    a' <- typeOf gctx ctx a
    b' <- typeOf gctx ctx b
    case cmpTypes (M.keys gctx ++ M.keys ctx) a' b' of
        Just o | o == EQ -> typeOf gctx ctx $ unNorm $ reify (M.keys gctx ++ M.keys ctx) a' (Stype maxBound)
        _ -> Left ["Types differ"]
typeOf _ _ Nat = Right $ Stype (Finite 0)
typeOf _ _ (Universe (U t)) = Right $ Stype $ succ (parseLevel t)
typeOf gctx ctx (App e1 e2) = do
    t <- typeOf gctx ctx e1
    case t of
        Spi _ a b -> hasType gctx ctx e2 a >> Right (b $ evalOfType gctx e2 a 0 $ ctxtToCtx ctx)
        _ -> Left ["Expected pi type\nActual type: " ++ show (reify (M.keys gctx ++ M.keys ctx) t $ Stype maxBound)]
typeOf _ _ (Var NoArg) = Left ["Expected identifier"]
typeOf gctx ctx (Var (Arg (PIdent (_,x)))) =
    maybe (Left ["Unknown identifier " ++ x]) Right $ M.lookup x ctx `mplus` fmap snd (M.lookup x gctx)
typeOf _ _ Suc = Right (sarr Snat Snat)
typeOf _ _ (NatConst x) = Right Snat
typeOf _ _ Rec = Right $ Spi "P" (Snat `sarr` Stype maxBound) $ \p -> app 0 p Szero `sarr`
    (Spi "x" Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x

typeOfLam :: Ctx -> CtxT -> Expr -> Value -> Err Value
typeOfLam gctx ctx (Lam [] e) t = typeOfLam gctx ctx e t
typeOfLam gctx ctx (Lam (x:xs) e) t =
    let (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) (unBinder x) (Lam xs e)
    in do
        s <- typeOf gctx (M.insert x' t ctx) e'
        if elem x' $ freeVars $ unNorm $ reify (x' : M.keys gctx ++ M.keys ctx) s (Stype maxBound)
            then Left ["Cannot infer type of lambda expression"]
            else Right s
typeOfLam gctx ctx e ty = do
    t <- typeOf gctx ctx e
    case t of
        Spi x a b -> do
            when (cmpTypes (M.keys gctx ++ M.keys ctx) a ty /= Just EQ) $
                Left ["Expected type: " ++ show (reify (M.keys gctx ++ M.keys ctx) a  $ Stype maxBound) ++
                      "\nActual type: " ++ show (reify (M.keys gctx ++ M.keys ctx) ty $ Stype maxBound)]
            let x' = freshName x (M.keys gctx ++ M.keys ctx)
                b' = b $ liftValue [x'] (svar x') a
            if elem x' $ freeVars $ unNorm $ reify (x' : M.keys gctx ++ M.keys ctx) b' (Stype maxBound)
                then Left ["Expected arrow type\nActual type: " ++
                    show (reify (M.keys gctx ++ M.keys ctx) (Spi x a b) $ Stype maxBound)]
                else Right b'
        _ -> Left ["Expected pi type\nActual type: " ++ show (reify (M.keys gctx ++ M.keys ctx) t $ Stype maxBound)]

hasType :: Ctx -> CtxT -> Expr -> Value -> Err ()
hasType gctx ctx (Lam [] e) ty = hasType gctx ctx e ty
hasType gctx ctx (Lam (x:xs) e) (Spi z a b) =
    let (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) (unBinder x) (Lam xs e)
    in hasType gctx (M.insert x' a ctx) e' (b $ liftValue [x'] (svar x') a)
hasType gctx ctx (Lam (Binder (Arg (PIdent (i,_))):_) _) ty = Left ["Expected pi type\nActual type: "
    ++ show (reify (M.keys gctx ++ M.keys ctx) ty $ Stype maxBound)]
hasType gctx ctx Idp (Spi x a b) =
    let x' = freshName x (M.keys gctx ++ M.keys ctx)
        x'' = liftValue [x'] (svar x') a
    in case b x'' of
        Sid t l r | cmpTypes (x' : M.keys gctx ++ M.keys ctx) a t == Just EQ -> do
            cmpValues (x' : M.keys gctx ++ M.keys ctx) l x'' t
            cmpValues (x' : M.keys gctx ++ M.keys ctx) r x'' t
        t -> Left ["Expected Id " ++ show (reify (x' : M.keys gctx ++ M.keys ctx) a $ Stype maxBound) ++ " " ++ x' ++ " "
                ++ x' ++ "\nActual type: " ++ show (reify (x' : M.keys gctx ++ M.keys ctx) t $ Stype maxBound)]
hasType gctx ctx Idp ty = Left ["Expected pi type\nActual type: " ++
    show (reify (M.keys gctx ++ M.keys ctx) ty $ Stype maxBound)]
hasType gctx ctx (Pmap e) (Spi x a@(Sid t l r) b) =
    let x' = freshName x (M.keys gctx ++ M.keys ctx)
    in case b (liftValue [x'] (svar x') a) of
        Sid s l' r' -> do
            hasType gctx ctx e (sarr t s)
            let e' = evalOfType gctx e (sarr t s) 0 (ctxtToCtx ctx)
            cmpValues (x' : M.keys gctx ++ M.keys ctx) l' (app 0 e' l) s
            cmpValues (x' : M.keys gctx ++ M.keys ctx) r' (app 0 e' r) s
        b' -> Left ["Expected Id type\nActual type: " ++ show (reify (M.keys gctx ++ M.keys ctx) b' $ Stype maxBound)]
hasType gctx ctx (Pmap _) (Spi x a _) = Left ["Expected Id type\nActual type: "
    ++ show (reify (M.keys gctx ++ M.keys ctx) a $ Stype maxBound)]
hasType gctx ctx (Pmap _) ty = Left ["Expected pi type\nActual type: "
    ++ show (reify (M.keys gctx ++ M.keys ctx) ty $ Stype maxBound)]
hasType gctx ctx e ty = do
    ty1 <- typeOf gctx ctx e
    case cmpTypes (M.keys gctx ++ M.keys ctx) ty1 ty of
        Just o | o /= GT -> Right ()
        _ -> Left ["Expected type: " ++ show (reify (M.keys gctx ++ M.keys ctx) ty  $ Stype maxBound) ++ "\n" ++
                    "Actual type: "  ++ show (reify (M.keys gctx ++ M.keys ctx) ty1 $ Stype maxBound)]

evalDecl :: String -> Expr -> Maybe Expr -> StateT (Ctx,Ctx) (Either [String]) (Value,Value)
evalDecl name expr mty = do
    (gctx,ctx) <- get
    let ctxt = ctxToCtxt ctx
    tv <- case mty of
        Nothing -> lift (typeOf gctx ctxt expr)
        Just ty -> do
            vty <- lift (typeOf gctx ctxt ty)
            case vty of
                Stype _ -> return $ eval gctx ty 0 ctx
                _ -> lift $ Left ["Expected type"]
    lift (hasType gctx ctxt expr tv)
    let ev = evalOfType gctx expr tv 0 ctx
    put (M.insert name (ev,tv) gctx, M.delete name ctx)
    return (ev,tv)

eval :: Ctx -> Expr -> Integer -> Ctx -> Value
eval gctx (Let defs e) n ctx =
    let decls = either internalError id (processDefs defs)
        st = forM_ decls $ \(name,ty,args,expr) -> evalDecl name (Lam (map Binder args) expr) ty
        (gctx',ctx') = either internalError id $ execStateT st (gctx, ctx)
    in eval gctx' e n ctx'
eval gctx (App Idp e) n ctx = eval (M.map (\(v,t) -> (idp v,t)) gctx) e (n + 1) (M.map (\(v,t) -> (idp v,t)) ctx)
eval gctx (App (Pmap e1) e2) n ctx = pmap n (eval gctx e1 n ctx) (eval gctx e2 n ctx)
eval gctx (Arr e1 e2) 0 ctx = sarr (eval gctx e1 0 ctx) (eval gctx e2 0 ctx)
eval gctx (Prod e1 e2) 0 ctx = sprod (eval gctx e1 0 ctx) (eval gctx e2 0 ctx)
eval gctx (Pi [] e) n ctx = eval gctx e n ctx
eval gctx (Sigma [] e) n ctx = eval gctx e n ctx
eval gctx (Pi (TypedVar (Var NoArg) t : vars) e) n ctx = eval gctx (Arr t (Pi vars e)) n ctx
eval gctx (Sigma (TypedVar (Var NoArg) t : vars) e) n ctx = eval gctx (Prod t (Sigma vars e)) n ctx
eval gctx (Pi (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval gctx t 0 ctx
      (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (Pi vars e)
  in Spi x' v1 $ \a -> eval gctx e' 0 (M.insert x' (a,v1) ctx)
eval gctx (Sigma (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval gctx t 0 ctx
      (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (Sigma vars e)
  in Ssigma x' v1 $ \a -> eval gctx e' 0 (M.insert x' (a,v1) ctx)
eval gctx (Id a b) 0 ctx =
    Sid (either (const internalError) id $ typeOf gctx (ctxToCtxt ctx) a) (eval gctx a 0 ctx) (eval gctx b 0 ctx)
eval _ Nat 0 _ = Snat
eval _ (Universe (U t)) 0 _ = Stype (parseLevel t)
eval gctx (App e1 e2) n ctx = 
    let Right (Spi _ a _) = typeOf gctx (ctxToCtxt ctx) e1
    in app n (eval gctx e1 n ctx) (evalOfType gctx e2 a n ctx)
eval gctx (Var (Arg (PIdent (_,x)))) _ ctx = fst $ fromJust $ M.lookup x ctx `mplus` M.lookup x gctx
eval _ Suc _ _ = Slam "n" $ \_ _ -> Ssuc
eval _ (NatConst x) _ _ = genConst x
  where genConst 0 = Szero
        genConst n = Ssuc $ genConst (n - 1)
eval gctx Rec _ ctx = Slam "P" $ \pk pm pv -> Slam "z" $ \zk zm zv -> Slam "s" $ \sk sm sv -> Slam "x" $ \xk xm ->
    rec (M.keys gctx ++ M.keys ctx) xk (action xm $ action sm $ action zm pv) (action xm $ action sm zv) (action xm sv)

evalOfType :: Ctx -> Expr -> Value -> Integer -> Ctx -> Value
evalOfType gctx (Lam [] e) ty n ctx = evalOfType gctx e ty n ctx
evalOfType gctx (Lam (Binder NoArg:xs) e) (Spi _ a b) n ctx = Slam "_" $ \k m v ->
    evalOfType (M.map (\(v,t) -> (action m v,t)) gctx) (Lam xs e) (b v) k $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType gctx (Lam (Binder (Arg (PIdent (_,x))):xs) e) (Spi _ a b) n ctx =
    let (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (Lam xs e)
    in Slam x' $ \k m v -> evalOfType (M.map (\(v,t) -> (action m v,t)) gctx) e' (b v) k
        $ M.insert x' (v,a) $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType gctx Idp t@(Spi x _ _) n ctx =
    let x' = Arg $ PIdent ((-1,-1), if x == "_" then "x" else x)
    in evalOfType gctx (Lam [Binder x'] $ App Idp $ Var x') t n ctx
evalOfType gctx (Pmap e) t@(Spi x _ _) n ctx =
    let x' = Arg $ PIdent ((-1,-1), freshName x $ freeVars e)
    in evalOfType gctx (Lam [Binder x'] $ App (Pmap e) $ Var x') t n ctx
evalOfType gctx e _ n ctx = eval gctx e n ctx

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) = f n []

rec :: [String] -> Integer -> Value -> Value -> Value -> Value -> Value
rec ctx n p z s = go
  where
    go Szero = z
    go (Ssuc x) = app n (app n s x) (go x)
    go t@(Ne (Norm e)) =
        let r = Rec $$ unNorm (reify ctx p $ Snat `sarr` Stype maxBound)
                    $$ unNorm (reify ctx z $ app n p Szero)
                    $$ unNorm (reify ctx s $ Spi "x" Snat $ \x -> app n p x `sarr` app n p (Ssuc x))
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
cmpTypes ctx (Sid t a b) (Sid t' a' b') = case cmpTypes ctx t t' of
    Nothing -> Nothing
    Just GT -> case (cmpValues ctx a a' t, cmpValues ctx b b' t) of
        (Right _, Right _) -> Just EQ
        _ -> Nothing
    _ -> case (cmpValues ctx a a' t', cmpValues ctx b b' t') of
        (Right _, Right _) -> Just EQ
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
liftValue fv e@(Ne _) (Spi x a _) = Slam x $ \k m v ->
    let Ne (Norm e') = action m e
    in Ne $ Norm $ App e' $ unNorm (reify fv v a)
liftValue _ t _ = t

reify :: [String] -> Value -> Value -> Norm
reify ctx (Slam x f) (Spi _ a b) =
    let x' = freshName x ctx
        bnd = [Binder $ Arg $ PIdent ((0,0),x')]
    in Norm $ Lam bnd $ unNorm $ reify (x':ctx) (f 0 [] $ liftValue [x'] (svar x') a) $ b (svar x')
reify _ Szero Snat = Norm (NatConst 0)
reify ctx Szero (Sid t _ _) = Norm $ App Idp $ unNorm (reify ctx Szero t)
reify ctx (Ssuc e) Snat = case reify ctx e Snat of
    Norm (NatConst n) -> Norm $ NatConst (n + 1)
    Norm t -> Norm (App Suc t)
reify ctx e@(Ssuc _) (Sid t _ _) = Norm $ App Idp $ unNorm (reify ctx e t)
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
reify ctx (Sidp x) (Sid t _ _) = Norm $ App Idp $ unNorm (reify ctx x t)
reify _ (Ne e) _ = e

internalError :: a
internalError = error "INTERNAL_ERROR"
