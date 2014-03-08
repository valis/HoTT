module Eval
    ( eval, evalOfType, evalDecl
    , typeOf, hasType
    , processDefs
    , reify
    , Value(..), Norm(..)
    , unBinder, getPos, argGetPos
    , Ctx, CtxT
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.State

import Parser.AbsGrammar
import Parser.PrintGrammar(printTree)
import ErrorDoc

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Level = Finite Integer | Omega | Omega1 | Omega2 deriving Eq
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

instance Pretty Norm where
    pretty = text . printTree . unNorm

expType :: Int -> [String] -> Value -> Doc
expType l ctx ty = text "Expected type:" <+> prettyLevel l (unNorm $ reify ctx ty $ Stype maxBound)

getPos :: Expr -> (Int,Int)
getPos (Let [] e) = getPos e
getPos (Let (Def (PIdent (p,_)) _ _ : _) _) = p
getPos (Let (DefType (PIdent (p,_)) _ : _) _) = p
getPos (Lam (PLam (p,_)) _ _) = p
getPos (Arr e _) = getPos e
getPos (Prod e _) = getPos e
getPos (Pi [] e) = getPos e
getPos (Pi (TypedVar (PPar (p,_)) _ _ : _) _) = p
getPos (Sigma [] e) = getPos e
getPos (Sigma (TypedVar (PPar (p,_)) _ _ : _) _) = p
getPos (Id e _) = getPos e
getPos (App e _) = getPos e
getPos (Var (NoArg (Pus (p,_)))) = p
getPos (Var (Arg (PIdent (p,_)))) = p
getPos (Nat (PNat (p,_))) = p
getPos (Suc (PSuc (p,_))) = p
getPos (Rec (PR (p,_))) = p
getPos (Idp (PIdp (p,_))) = p
getPos (Pmap (Ppmap (p,_)) _) = p
getPos (NatConst (PInt (p,_))) = p
getPos (Universe (U (p,_))) = p
getPos (Paren (PPar (p,_)) _) = p

snorm :: Expr -> Value
snorm = Ne . Norm

svar :: String -> Value
svar x = snorm $ Var $ Arg $ PIdent ((-1,-1),x)

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

type Err a = Either [Doc] a

processDefs :: [Def] -> Err [(String,Maybe Expr,[Arg],Expr)]
processDefs defs =
    let typeSigs = filterTypeSigs defs
        funDecls = filterFunDecls defs
        typeSigs' = map (\(PIdent (_,s),e) -> (s,e)) typeSigs
        funDecls' = map (\(PIdent (_,s),e) -> (s,e)) funDecls
        typeSigsDup = duplicates (map fst typeSigs)
        funDeclsDup = duplicates (map fst funDecls)
    in if not (null typeSigsDup) || not (null funDeclsDup)
        then Left $ map (\(PIdent ((l,c),s)) -> textLC l c $ "Duplicate type signatures for " ++ s) typeSigsDup
                 ++ map (\(PIdent ((l,c),s)) -> textLC l c $ "Multiple declarations of " ++ s) funDeclsDup
        else Right $ map (\(name,(args,expr)) -> (name,lookup name typeSigs',args,expr)) funDecls'
  where
    filterTypeSigs :: [Def] -> [(PIdent,Expr)]
    filterTypeSigs [] = []
    filterTypeSigs (DefType x e : defs) = (x,e) : filterTypeSigs defs
    filterTypeSigs (_:defs) = filterTypeSigs defs
    
    filterFunDecls :: [Def] -> [(PIdent,([Arg],Expr))]
    filterFunDecls [] = []
    filterFunDecls (Def x a e : defs) = (x,(a,e)) : filterFunDecls defs
    filterFunDecls (_:defs) = filterFunDecls defs
    
    duplicates :: [PIdent] -> [PIdent]
    duplicates [] = []
    duplicates (x@(PIdent (_,v)) : xs) = case findRemove xs of
        Nothing -> duplicates xs
        Just xs' -> x : duplicates xs'
      where
        findRemove :: [PIdent] -> Maybe [PIdent]
        findRemove [] = Nothing
        findRemove (y@(PIdent (_,w)) : ys)
            | v == w = Just $ maybe ys id (findRemove ys)
            | otherwise = fmap (y:) (findRemove ys)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

idp :: Value -> Value
idp = action [Ud]

pmap :: Integer -> Value -> Value -> Value
pmap n f = app (n + 1) (idp f)

unArg :: Arg -> String
unArg (NoArg _) = "_"
unArg (Arg (PIdent (_,x))) = x

argGetPos :: Arg -> (Int,Int)
argGetPos (NoArg (Pus (p,_))) = p
argGetPos (Arg (PIdent (p,_))) = p

unBinder :: Binder -> String
unBinder (Binder b) = unArg b

binderGetPos :: Binder -> (Int,Int)
binderGetPos (Binder b) = argGetPos b

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
freeVars (Lam _ bnds e) = freeVars e \\ map unBinder bnds
freeVars (Arr e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pi [] e) = freeVars e
freeVars (Pi (TypedVar _ (Var (NoArg _)) t : xs) e) = freeVars t `union` freeVars (Pi xs e)
freeVars (Pi (TypedVar _ (Var (Arg (PIdent (_,x)))) t : xs) e) = freeVars t `union` delete x (freeVars $ Pi xs e)
freeVars (Prod e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Sigma [] e) = freeVars e
freeVars (Sigma (TypedVar _ (Var (NoArg _)) t : xs) e) = freeVars t `union` freeVars (Sigma xs e)
freeVars (Sigma (TypedVar _ (Var (Arg (PIdent (_,x)))) t : xs) e) = freeVars t `union` delete x (freeVars $ Sigma xs e)
freeVars (Id e1 e2) = freeVars e1 `union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var (Arg (PIdent (_,x)))) = [x]
freeVars (Var (NoArg _)) = []
freeVars (Nat _) = []
freeVars (Suc _) = []
freeVars (Rec _) = []
freeVars (Idp _) = []
freeVars (Pmap _ e) = freeVars e
freeVars (NatConst _) = []
freeVars (Universe _) = []
freeVars (Paren _ e) = freeVars e

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
            Lam _ as' t' = rename (Lam internalError (map Binder as) t) x y
        in (Def (PIdent (i,y')) (map (\(Binder a) -> a) as') t' : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
            Lam _ as' t' = rename (Lam internalError (map Binder as) t) x y
        in (Def (PIdent (i,z)) (map (\(Binder a) -> a) as') t' : defs', e')

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename (Let defs e) x y = let (defs',e') = renameDefs defs e x y in Let defs' e'
rename e@(Lam i bs e1) x y
    | elem x bs' = e
    | elem y bs' = Lam i (map (\y1 -> if unBinder y1 == y then renameBinder y1 y' else y1) bs) (rename e' x y)
    | otherwise = Lam i bs (rename e1 x y)
  where
    bs' = map unBinder bs
    (y',e') = renameExpr (x:bs') y e1
    renameBinder :: Binder -> String -> Binder
    renameBinder b@(Binder (NoArg _)) _ = b
    renameBinder (Binder (Arg (PIdent (i,_)))) x = Binder $ Arg $ PIdent (i,x)
rename (Arr e1 e2) x y = Arr (rename e1 x y) (rename e2 x y)
rename (Pi [] e) x y = rename e x y
rename (Pi (TypedVar p (Var (Arg (PIdent (i,z)))) t : bs) e) x y | x == z
    = Pi [TypedVar p (Var (Arg (PIdent (i,z)))) (rename t x y)] (Pi bs e)
rename (Pi (TypedVar p v t : bs) e) x y = Pi [TypedVar p v (rename t x y)] $ rename (Pi bs e) x y
rename (Prod e1 e2) x y = Prod (rename e1 x y) (rename e2 x y)
rename (Sigma [] e) x y = rename e x y
rename (Sigma (TypedVar p (Var (Arg (PIdent (i,z)))) t : bs) e) x y | x == z
    = Sigma [TypedVar p (Var (Arg (PIdent (i,z)))) (rename t x y)] (Sigma bs e)
rename (Sigma (TypedVar p v t : bs) e) x y = Sigma [TypedVar p v (rename t x y)] $ rename (Sigma bs e) x y
rename (Id e1 e2) x y = Id (rename e1 x y) (rename e2 x y)
rename (App e1 e2) x y = App (rename e1 x y) (rename e2 x y)
rename (Var (Arg (PIdent (i,z)))) x y | x == z = Var $ Arg $ PIdent (i,y)
rename e@(Var _) _ _ = e
rename e@(Nat _) _ _ = e
rename e@(Suc _) _ _ = e
rename e@(Rec _) _ _ = e
rename e@(Idp _) _ _ = e
rename (Pmap i e) x y = Pmap i (rename e x y)
rename e@(NatConst _) _ _ = e
rename e@(Universe _) _ _ = e
rename (Paren i e) x y = Paren i (rename e x y)

liftErr2 :: (a -> b -> Err c) -> Err a -> Err b -> Err c
liftErr2 f (Left m1) (Left m2) = Left (m1 ++ m2)
liftErr2 f (Left m) _ = Left m
liftErr2 f _ (Left m) = Left m
liftErr2 f (Right v1) (Right v2) = f v1 v2

maxType :: (Int,Int) -> (Int,Int) -> [String] -> Value -> Value -> Err Value
maxType _ _ _ (Stype k1) (Stype k2) = Right $ Stype (max k1 k2)
maxType (l,c) (l',c') ctx t1 t2 = liftErr2 internalError
    (cmpTypesErr l  c  ctx (Stype $ pred maxBound) t1)
    (cmpTypesErr l' c' ctx (Stype $ pred maxBound) t2)

typeOf'depType :: Ctx -> ([TypedVar] -> Expr -> Expr) -> CtxT -> [TypedVar] -> Expr -> Err Value
typeOf'depType gctx _ ctx [] e = typeOf gctx ctx e
typeOf'depType gctx dt ctx (TypedVar _ vars t : list) e = getVars vars >>= go
  where
    tv = typeOf gctx ctx t
    
    getVars (Var (NoArg _)) = Right ["_"]
    getVars (Var (Arg (PIdent (_,x)))) = Right [x]
    getVars (App a (Var (NoArg _))) = fmap (++ ["_"]) (getVars a)
    getVars (App a (Var (Arg (PIdent (_,x))))) = fmap (++ [x]) (getVars a)
    getVars e = let (l,c) = getPos e in Left [textLC l c "Expected identifier"]
    
    go [] = typeOf'depType gctx dt ctx list e
    go [v] =
        let k1 = typeOf gctx ctx t
            (v',e') = renameExpr (M.keys gctx ++ M.keys ctx) v (dt list e)
            k2 = typeOf gctx (M.insert v' (eval gctx t 0 (ctxtToCtx ctx)) ctx) e'
        in liftErr2 (maxType (getPos t) (getPos e) $ M.keys gctx ++ M.keys ctx) k1 k2
    go _ = undefined

typeOf :: Ctx -> CtxT -> Expr -> Err Value
typeOf gctx ctx (Lam _ [] e) = typeOf gctx ctx e
typeOf _ _ (Lam (PLam ((l,c),_)) _ _) = Left [textLC l c "Cannot infer type of the argument"]
typeOf _ _ (Idp (PIdp ((l,c),_))) = Left [textLC l c "Cannot infer type of idp"]
typeOf _ _ (Pmap (Ppmap ((l,c),_)) _) = Left [textLC l c "Cannot infer type of pmap"]
typeOf gctx ctx (Let defs e) = do
    decls <- processDefs defs
    let st = forM_ decls $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    (gctx',ctx') <- execStateT st (gctx, ctxtToCtx ctx)
    typeOf gctx' (ctxToCtxt ctx') e
typeOf gctx ctx (App (Idp _) e) = do
    t <- typeOf gctx ctx e
    let v = eval gctx e 0 (ctxtToCtx ctx)
    Right (Sid t v v)
typeOf gctx ctx (App (Pmap (Ppmap ((l,c),_)) e1) e2) = do
    t2 <- typeOf gctx ctx e2
    case t2 of
        Sid t a b -> do
            s <- typeOfLam (l,c) (getPos e2) gctx ctx e1 t2
            let e' = app 0 $ evalOfType gctx e1 (sarr t s) 0 (ctxtToCtx ctx)
            Right $ Sid s (e' a) (e' b)
        _ -> let (l',c') = getPos e2 in Left [docLC l' c' $ text "Expected Id type" $$
            text "Actual type:" <+> prettyHead (unNorm $ reify (M.keys gctx ++ M.keys ctx) t2 $ Stype maxBound)]
typeOf gctx ctx (Arr e1 e2) =
    liftErr2 (maxType (getPos e1) (getPos e2) $ M.keys gctx ++ M.keys ctx) (typeOf gctx ctx e1) (typeOf gctx ctx e2)
typeOf gctx ctx (Prod e1 e2) = typeOf gctx ctx (Arr e1 e2)
typeOf gctx ctx (Pi tv e) = typeOf'depType gctx Pi ctx tv e
typeOf gctx ctx (Sigma tv e) = typeOf'depType gctx Sigma ctx tv e
typeOf gctx ctx (Id a b) = do
    a' <- typeOf gctx ctx a
    b' <- typeOf gctx ctx b
    let (l,c) = getPos b
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) a' b'
    typeOf gctx ctx $ unNorm $ reify (M.keys gctx ++ M.keys ctx) a' (Stype maxBound)
typeOf _ _ (Nat _) = Right $ Stype (Finite 0)
typeOf _ _ (Universe (U (_,t))) = Right $ Stype $ succ (parseLevel t)
typeOf gctx ctx (App e1 e2) = do
    t <- typeOf gctx ctx e1
    case t of
        Spi _ a b -> hasType gctx ctx e2 a >> Right (b $ evalOfType gctx e2 a 0 $ ctxtToCtx ctx)
        _ -> let (l,c) = getPos e1 in Left [docLC l c $ text "Expected pi type" $$
            text "Actual type: " <+> prettyHead (unNorm $ reify (M.keys gctx ++ M.keys ctx) t $ Stype maxBound)]
typeOf _ _ (Var (NoArg (Pus ((l,c),_)))) = Left [textLC l c "Expected identifier"]
typeOf gctx ctx (Var (Arg (PIdent ((l,c),x)))) =
    maybe (Left [textLC l c $ "Unknown identifier " ++ x]) Right $ M.lookup x ctx `mplus` fmap snd (M.lookup x gctx)
typeOf _ _ (Suc _) = Right (sarr Snat Snat)
typeOf _ _ (NatConst _) = Right Snat
typeOf _ _ (Rec _) = Right $ Spi "P" (Snat `sarr` Stype maxBound) $ \p -> app 0 p Szero `sarr`
    (Spi "x" Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOf gctx ctx (Paren _ e) = typeOf gctx ctx e

typeOfLam :: (Int,Int) -> (Int,Int) -> Ctx -> CtxT -> Expr -> Value -> Err Value
typeOfLam lc lc' gctx ctx (Lam _ [] e) ty = typeOfLam lc lc' gctx ctx e ty
typeOfLam _ _ gctx ctx (Lam (PLam ((l,c),_)) (x:xs) e) (Sid ty _ _) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) (unBinder x) (Lam (PLam (p,"\\")) xs e)
    in do
        s <- typeOf gctx (M.insert x' ty ctx) e'
        if elem x' $ freeVars $ unNorm $ reify (x' : M.keys gctx ++ M.keys ctx) s (Stype maxBound)
            then Left [textLC l c "Cannot infer type of lambda expression"]
            else Right s
typeOfLam lc lc' gctx ctx (Paren _ e) act = typeOfLam lc lc' gctx ctx e act
typeOfLam (l,c) (l',c') gctx ctx e (Sid act _ _) = do
    let fv = M.keys gctx ++ M.keys ctx
    t <- typeOf gctx ctx e
    case t of
        Spi x exp r -> do
            case cmpTypes fv exp act of
                Just o | o /= LT -> Right ()
                _ -> let em s t = text s <+> parens (pretty $ reify fv t $ Stype maxBound) <+> text "_" <+> text "_"
                     in Left [docLC l' c' $ em "Expected type: Id" exp $$ em "Actual type: Id" act]
            let x' = freshName x (M.keys gctx ++ M.keys ctx)
                r' = r $ liftValue [x'] (svar x') exp
            if elem x' $ freeVars $ unNorm $ reify (x' : fv) r' (Stype maxBound)
                then Left [docLC l c $ text "Expected arrow type" $$
                    text "Actual type:" <+> pretty (reify fv t $ Stype maxBound)]
                else Right r'
        _ -> Left [docLC l c $ text "Expected pi type" $$
            text "Actual type:" <+> prettyHead (unNorm $ reify fv t $ Stype maxBound)]

hasType :: Ctx -> CtxT -> Expr -> Value -> Err ()
hasType gctx ctx (Lam _ [] e) ty = hasType gctx ctx e ty
hasType gctx ctx (Lam i (x:xs) e) (Spi z a b) =
    let (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) (unBinder x) (Lam i xs e)
    in hasType gctx (M.insert x' a ctx) e' (b $ liftValue [x'] (svar x') a)
hasType gctx ctx (Lam _ (Binder (Arg (PIdent ((l,c),_))):_) _) ty =
    Left [docLC l c $ expType 1 (M.keys gctx ++ M.keys ctx) ty $$ text "But lambda expression has pi type"]
hasType gctx ctx (Idp (PIdp ((l,c),_))) exp@(Spi x a _) =
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) exp (Spi x a $ \v -> Sid a v v)
hasType gctx ctx (Idp (PIdp ((l,c),_))) ty =
    Left [docLC l c $ expType 1 (M.keys gctx ++ M.keys ctx) ty $$ text "But idp has pi type"]
hasType gctx ctx (Pmap (Ppmap ((l,c),_)) e) exp@(Spi x (Sid t a b) r) =
    let x' = freshName x (M.keys gctx ++ M.keys ctx)
    in case r (liftValue [x'] (svar x') a) of
        Sid s _ _ -> do
            hasType gctx ctx e (sarr t s)
            let e' = evalOfType gctx e (sarr t s) 0 (ctxtToCtx ctx)
                act = Sid t a b `sarr` Sid s (app 0 e' a) (app 0 e' b)
            cmpTypesErr l c (M.keys gctx ++ M.keys ctx) exp act
        _ -> Left [docLC l c $ expType 2 (M.keys gctx ++ M.keys ctx) exp $$
            text "But pmap _ has type of the form x = y -> _ x = _ y"]
hasType gctx ctx (Pmap (Ppmap ((l,c),_)) _) exp@(Spi _ _ _) =
    Left [docLC l c $ expType 2 (M.keys gctx ++ M.keys ctx) exp $$
        text "But pmap _ has type of the form x = y -> _ x = _ y"]
hasType gctx ctx (Pmap (Ppmap ((l,c),_)) _) exp =
    Left [docLC l c $ expType 1 (M.keys gctx ++ M.keys ctx) exp $$ text "But pmap _ has pi type"]
hasType gctx ctx (Paren _ e) ty = hasType gctx ctx e ty
hasType gctx ctx e ty = do
    ty1 <- typeOf gctx ctx e
    let (l,c) = getPos e
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) ty ty1

evalDecl :: String -> Expr -> Maybe Expr -> StateT (Ctx,Ctx) (Either [Doc]) (Value,Value)
evalDecl name expr mty = do
    (gctx,ctx) <- get
    let ctxt = ctxToCtxt ctx
    tv <- case mty of
        Nothing -> lift (typeOf gctx ctxt expr)
        Just ty -> do
            vty <- lift (typeOf gctx ctxt ty)
            let (l,c) = getPos ty
            lift $ cmpTypesErr l c (M.keys gctx ++ M.keys ctx) (Stype $ pred maxBound) vty
            return (eval gctx ty 0 ctx)
    lift (hasType gctx ctxt expr tv)
    let ev = evalOfType gctx expr tv 0 ctx
    put (M.insert name (ev,tv) gctx, M.delete name ctx)
    return (ev,tv)

eval :: Ctx -> Expr -> Integer -> Ctx -> Value
eval gctx (Let defs e) n ctx =
    let decls = either internalError id (processDefs defs)
        st = forM_ decls $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
        (gctx',ctx') = either internalError id $ execStateT st (gctx, ctx)
    in eval gctx' e n ctx'
eval gctx (App (Idp _) e) n ctx = eval (M.map (\(v,t) -> (idp v,t)) gctx) e (n + 1) (M.map (\(v,t) -> (idp v,t)) ctx)
eval gctx (App (Pmap _ e1) e2) n ctx = pmap n (eval gctx e1 n ctx) (eval gctx e2 n ctx)
eval gctx (Arr e1 e2) 0 ctx = sarr (eval gctx e1 0 ctx) (eval gctx e2 0 ctx)
eval gctx (Prod e1 e2) 0 ctx = sprod (eval gctx e1 0 ctx) (eval gctx e2 0 ctx)
eval gctx (Pi [] e) n ctx = eval gctx e n ctx
eval gctx (Sigma [] e) n ctx = eval gctx e n ctx
eval gctx (Pi (TypedVar _ (Var (NoArg _)) t : vars) e) n ctx = eval gctx (Arr t (Pi vars e)) n ctx
eval gctx (Sigma (TypedVar _ (Var (NoArg _)) t : vars) e) n ctx = eval gctx (Prod t (Sigma vars e)) n ctx
eval gctx (Pi (TypedVar _ (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval gctx t 0 ctx
      (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (Pi vars e)
  in Spi x' v1 $ \a -> eval gctx e' 0 (M.insert x' (a,v1) ctx)
eval gctx (Sigma (TypedVar _ (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx =
  let v1 = eval gctx t 0 ctx
      (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (Sigma vars e)
  in Ssigma x' v1 $ \a -> eval gctx e' 0 (M.insert x' (a,v1) ctx)
eval gctx (Id a b) 0 ctx =
    Sid (either (const internalError) id $ typeOf gctx (ctxToCtxt ctx) a) (eval gctx a 0 ctx) (eval gctx b 0 ctx)
eval _ (Nat _) 0 _ = Snat
eval _ (Universe (U (_,t))) 0 _ = Stype (parseLevel t)
eval gctx (App e1 e2) n ctx = 
    let Right (Spi _ a _) = typeOf gctx (ctxToCtxt ctx) e1
    in app n (eval gctx e1 n ctx) (evalOfType gctx e2 a n ctx)
eval gctx (Var (Arg (PIdent (_,x)))) _ ctx = fst $ fromJust $ M.lookup x ctx `mplus` M.lookup x gctx
eval _ (Suc _) _ _ = Slam "n" $ \_ _ -> Ssuc
eval _ (NatConst (PInt (_,x))) _ _ = genConst (read x :: Integer)
  where genConst 0 = Szero
        genConst n = Ssuc $ genConst (n - 1)
eval gctx (Rec _) _ ctx = Slam "P" $ \pk pm pv -> Slam "z" $ \zk zm zv -> Slam "s" $ \sk sm sv -> Slam "x" $ \xk xm ->
    rec (M.keys gctx ++ M.keys ctx) xk (action xm $ action sm $ action zm pv) (action xm $ action sm zv) (action xm sv)
eval gctx (Paren _ e) n ctx = eval gctx e n ctx

evalOfType :: Ctx -> Expr -> Value -> Integer -> Ctx -> Value
evalOfType gctx (Lam _ [] e) ty n ctx = evalOfType gctx e ty n ctx
evalOfType gctx (Lam _ (Binder (NoArg _):xs) e) (Spi _ a b) n ctx = Slam "_" $ \k m v ->
    let p = PLam ((if null xs then getPos e else binderGetPos (head xs)),"\\")
    in evalOfType (M.map (\(v,t) -> (action m v,t)) gctx) (Lam p xs e) (b v) k $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType gctx (Lam _ (Binder (Arg (PIdent (_,x))):xs) e) (Spi _ a b) n ctx =
    let p = PLam ((if null xs then getPos e else binderGetPos (head xs)),"\\")
        (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) x (Lam p xs e)
    in Slam x' $ \k m v -> evalOfType (M.map (\(v,t) -> (action m v,t)) gctx) e' (b v) k
        $ M.insert x' (v,a) $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType gctx e@(Idp (PIdp p)) t@(Spi x _ _) n ctx =
    let x' = Arg $ PIdent ((-1,-1), if x == "_" then "x" else x)
    in evalOfType gctx (Lam (PLam p) [Binder x'] $ App e $ Var x') t n ctx
evalOfType gctx pm@(Pmap (Ppmap i) e) t@(Spi x _ _) n ctx =
    let x' = Arg $ PIdent ((-1,-1), freshName x $ freeVars e)
    in evalOfType gctx (Lam (PLam i) [Binder x'] $ App pm $ Var x') t n ctx
evalOfType gctx (Paren _ e) ty n ctx = evalOfType gctx e ty n ctx
evalOfType gctx e _ n ctx = eval gctx e n ctx

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) = f n []

infixl 5 `aApp`
aApp = App

rec :: [String] -> Integer -> Value -> Value -> Value -> Value -> Value
rec ctx n p z s = go
  where
    go Szero = z
    go (Ssuc x) = app n (app n s x) (go x)
    go t@(Ne (Norm e)) =
        let r = Rec (PR ((getPos e),"R"))
                `aApp` unNorm (reify ctx p $ Snat `sarr` Stype maxBound)
                `aApp` unNorm (reify ctx z $ app n p Szero)
                `aApp` unNorm (reify ctx s $ Spi "x" Snat $ \x -> app n p x `sarr` app n p (Ssuc x))
                `aApp` e
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
    Just GT -> if cmpValues ctx a a' t  && cmpValues ctx b b' t  then Just EQ else Nothing
    _       -> if cmpValues ctx a a' t' && cmpValues ctx b b' t' then Just EQ else Nothing
cmpTypes _ Snat Snat = Just EQ
cmpTypes _ (Stype k) (Stype k') = Just (compare k k')
cmpTypes _ (Ne t) (Ne t') = if t == t' then Just EQ else Nothing
cmpTypes _ _ _ = Nothing

cmpTypesErr :: Int -> Int -> [String] -> Value -> Value -> Err ()
cmpTypesErr l c ctx t1 t2 = case cmpTypes ctx t1 t2 of
    Just o | o /= LT -> Right ()
    _ -> Left [docLC l c $ expType (-1) ctx t1 $$ text "Actual type:" <+> pretty (reify ctx t2 $ Stype maxBound)]

cmpValues :: [String] -> Value -> Value -> Value -> Bool
cmpValues ctx e1 e2 t = reify ctx e1 t == reify ctx e2 t

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
        bnd = [Binder $ Arg $ PIdent ((-1,-1),x')]
    in Norm $ Lam (PLam ((-1,-1),"\\")) bnd $ unNorm $ reify (x':ctx) (f 0 [] $ liftValue [x'] (svar x') a) $ b (svar x')
reify _ Szero Snat = Norm (NatConst (PInt ((-1,-1),"0")))
reify ctx Szero (Sid t _ _) = Norm $ App (Idp $ PIdp ((-1,-1),"idp")) $ unNorm (reify ctx Szero t)
reify ctx (Ssuc e) Snat = case reify ctx e Snat of
    Norm (NatConst (PInt (p,n))) -> Norm $ NatConst $ PInt (p, show $ (read n :: Integer) + 1)
    Norm t -> Norm $ App (Suc $ PSuc ((-1,-1),"suc")) t
reify ctx e@(Ssuc _) (Sid t _ _) = Norm $ App (Idp $ PIdp ((-1,-1),"idp")) $ unNorm (reify ctx e t)
reify ctx (Spi x a b) (Stype l) =
    let x' = freshName x ctx
        bnd = [TypedVar (PPar ((-1,-1),"(")) (Var $ Arg $ PIdent ((-1,-1),x')) $ unNorm $ reify ctx a $ Stype l]
    in Norm $ Pi bnd $ unNorm $ reify (x':ctx) (b $ svar x') (Stype l)
reify ctx (Ssigma x a b) (Stype l) =
    let x' = freshName x ctx
        bnd = [TypedVar (PPar ((-1,-1),"(")) (Var $ Arg $ PIdent ((-1,-1),x')) $ unNorm $ reify ctx a $ Stype l]
    in Norm $ Sigma bnd $ unNorm $ reify (x':ctx) (b $ svar x') (Stype l)
reify ctx (Sid t a b) (Stype _) = Norm $ Id (unNorm $ reify ctx a t) (unNorm $ reify ctx b t)
reify _ (Stype (Finite k)) (Stype _) = Norm $ Universe $ U ((-1,-1), "Type" ++ show k)
reify _ (Stype Omega) (Stype _) = Norm $ Universe $ U ((-1,-1),"Type")
reify _ (Stype Omega1) (Stype _) = Norm $ Universe $ U ((-1,-1),"TYPE")
reify _ Snat (Stype _) = Norm $ Nat $ PNat ((-1,-1),"Nat")
reify ctx (Sidp x) (Sid t _ _) = Norm $ App (Idp $ PIdp ((-1,-1),"idp")) $ unNorm (reify ctx x t)
reify _ (Ne e) _ = e

internalError :: a
internalError = error "INTERNAL_ERROR"
