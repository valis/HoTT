module Eval
    ( eval, evalOfType, evalDecl
    , typeOf, hasType
    , processDefs
    , reify
    , Value(..)
    , unBinder, getPos, argGetPos
    , Ctx, CtxT
    ) where

import qualified Data.Map as M
import Data.Maybe
import Control.Monad
import Control.Monad.State

import Parser.AbsGrammar
import qualified Syntax.Term as T
import Syntax.Raw
import ErrorDoc

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi String Value (Value -> Value) | Ssigma String Value (Value -> Value) -- Constructors for Type_k
    | Snat | Sid Value Value Value | Stype T.Level -- Constructors for Type_k
    | Sidp Value -- Constructor for Id
    | Ne T.Term
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxT = M.Map String Value

expType :: Int -> [String] -> Value -> EDoc
expType l ctx ty = etext "Expected type:" <+> eprettyLevel l (reify ctx ty $ Stype maxBound)

svar :: String -> Value
svar x = Ne (T.Var x)

infixr 5 `sarr`
sarr :: Value -> Value -> Value
sarr a b = Spi "_" a (const b)

sprod :: Value -> Value -> Value
sprod a b = Ssigma "_" a (const b)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

idp :: Value -> Value
idp = action [Ud]

pmap :: Integer -> Value -> Value -> Value
pmap n f = app (n + 1) (idp f)

ctxtToCtx :: CtxT -> Ctx
ctxtToCtx = M.mapWithKey $ \k v -> (liftValue [k] (svar k) v, v)

ctxToCtxt :: Ctx -> CtxT
ctxToCtxt = M.map snd

liftErr2 :: (a -> b -> EDocM c) -> EDocM a -> EDocM b -> EDocM c
liftErr2 f (Left m1) (Left m2) = Left (m1 ++ m2)
liftErr2 f (Left m) _ = Left m
liftErr2 f _ (Left m) = Left m
liftErr2 f (Right v1) (Right v2) = f v1 v2

maxType :: (Int,Int) -> (Int,Int) -> [String] -> Expr -> Expr -> Value -> Value -> EDocM Value
maxType _ _ _ _ _ (Stype k1) (Stype k2) = Right $ Stype (max k1 k2)
maxType (l,c) (l',c') ctx e1 e2 t1 t2 = liftErr2 (error "maxType")
    (cmpTypesErr l  c  ctx (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr l' c' ctx (Stype $ pred maxBound) t2 e2)

typeOf'depType :: Ctx -> CtxT -> [TypedVar] -> Expr -> EDocM Value
typeOf'depType gctx ctx [] e = typeOf gctx ctx e
typeOf'depType gctx ctx (TypedVar _ vars t : list) e = do
    tv <- typeOf gctx ctx t
    let (l,c) = getPos t
        e' = Pi list e
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) (Stype $ pred maxBound) tv t
    ctx' <- updateCtx ctx (eval gctx t 0 $ ctxtToCtx ctx) vars
    ev <- typeOf gctx ctx' e'
    maxType (l,c) (getPos e) (M.keys gctx ++ M.keys ctx') t e' tv ev
  where
    updateCtx ctx _ (Var (NoArg _)) = Right ctx
    updateCtx ctx tv (Var (Arg (PIdent (_,x)))) = Right (M.insert x tv ctx)
    updateCtx ctx tv (App a (Var (NoArg _))) = updateCtx ctx tv a
    updateCtx ctx tv (App a (Var (Arg (PIdent (_,x))))) = fmap (M.insert x tv) (updateCtx ctx tv a)
    updateCtx _ _ e = let (l,c) = getPos e in Left [emsgLC l c "Expected identifier" enull]

typeOf :: Ctx -> CtxT -> Expr -> EDocM Value
typeOf gctx ctx (Lam _ [] e) = typeOf gctx ctx e
typeOf _ _ (Lam (PLam ((l,c),_)) _ _) = Left [emsgLC l c "Cannot infer type of the argument" enull]
typeOf _ _ (Idp (PIdp ((l,c),_))) = Left [emsgLC l c "Cannot infer type of idp" enull]
typeOf _ _ (Pmap (Ppmap ((l,c),_)) _) = Left [emsgLC l c "Cannot infer type of pmap" enull]
typeOf gctx ctx (Let defs e) = do
    decls <- processDefs defs
    let st = forM_ decls $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    (gctx',ctx') <- execStateT st (gctx, ctxtToCtx ctx)
    typeOf gctx' (ctxToCtxt ctx') e
typeOf gctx ctx (App (Idp _) e) = do
    t <- typeOf gctx ctx e
    let v = evalOfType gctx e t 0 (ctxtToCtx ctx)
    Right (Sid t v v)
typeOf gctx ctx (App (Pmap (Ppmap ((l,c),_)) e1) e2) = do
    t2 <- typeOf gctx ctx e2
    case t2 of
        Sid t a b -> do
            s <- typeOfLam (l,c) (getPos e2) gctx ctx e1 e2 t2
            let e' = app 0 $ evalOfType gctx e1 (sarr t s) 0 (ctxtToCtx ctx)
            Right $ Sid s (e' a) (e' b)
        _ -> let (l',c') = getPos e2
                 fv = M.keys gctx ++ M.keys ctx
             in Left [emsgLC l' c' "" $ etext "Expected Id type" $$ etext "But term" <+> epretty e2
                    <+> etext "has type" <+> eprettyHead (reify fv t2 $ Stype maxBound)]
typeOf gctx ctx (Arr e1 e2) =
    liftErr2 (maxType (getPos e1) (getPos e2) (M.keys gctx ++ M.keys ctx) e1 e2) (typeOf gctx ctx e1) (typeOf gctx ctx e2)
typeOf gctx ctx (Prod e1 e2) = typeOf gctx ctx (Arr e1 e2)
typeOf gctx ctx (Pi tv e) = typeOf'depType gctx ctx tv e
typeOf gctx ctx (Sigma tv e) = typeOf'depType gctx ctx tv e
typeOf gctx ctx (Id a b) = do
    a' <- typeOf gctx ctx a
    b' <- typeOf gctx ctx b
    let (l,c) = getPos b
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) a' b' b
    undefined -- typeOf gctx ctx $ unNorm $ reify (M.keys gctx ++ M.keys ctx) a' (Stype maxBound)
typeOf _ _ (Nat _) = Right $ Stype (T.Finite 0)
typeOf _ _ (Universe (U (_,t))) = Right $ Stype $ succ (parseLevel t)
typeOf gctx ctx (App e1 e2) = do
    t <- typeOf gctx ctx e1
    case t of
        Spi _ a b -> hasType gctx ctx e2 a >> Right (b $ evalOfType gctx e2 a 0 $ ctxtToCtx ctx)
        _ -> let (l,c) = getPos e1
                 fv = M.keys gctx ++ M.keys ctx
             in Left [emsgLC l c "" $ etext "Expected pi type" $$ etext "But term" <+> epretty e1
                    <+> etext "has type" <+> eprettyHead (reify fv t $ Stype maxBound)]
typeOf _ _ (Var (NoArg (Pus ((l,c),_)))) = Left [emsgLC l c "Expected identifier" enull]
typeOf gctx ctx (Var (Arg (PIdent ((l,c),x)))) =
    maybe (Left [emsgLC l c ("Unknown identifier " ++ x) enull]) Right $ M.lookup x ctx `mplus` fmap snd (M.lookup x gctx)
typeOf _ _ (Suc _) = Right (sarr Snat Snat)
typeOf _ _ (NatConst _) = Right Snat
typeOf _ _ (Rec _) = Right $ Spi "P" (Snat `sarr` Stype maxBound) $ \p -> app 0 p Szero `sarr`
    (Spi "x" Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOf gctx ctx (Paren _ e) = typeOf gctx ctx e

typeOfLam :: (Int,Int) -> (Int,Int) -> Ctx -> CtxT -> Expr -> Expr -> Value -> EDocM Value
typeOfLam lc lc' gctx ctx (Lam _ [] e) e2 ty = typeOfLam lc lc' gctx ctx e e2 ty
typeOfLam _ _ gctx ctx (Lam (PLam ((l,c),_)) (x:xs) e) _ (Sid ty _ _) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) (unBinder x) (Lam (PLam (p,"\\")) xs e)
    in do
        s <- typeOf gctx (M.insert x' ty ctx) e'
        undefined {- if elem x' $ freeVars $ unNorm $ reify (x' : M.keys gctx ++ M.keys ctx) s (Stype maxBound)
            then Left [emsgLC l c "Cannot infer type of lambda expression" enull]
            else Right s -}
typeOfLam lc lc' gctx ctx (Paren _ e) e2 act = typeOfLam lc lc' gctx ctx e e2 act
typeOfLam (l,c) (l',c') gctx ctx e e2 (Sid act _ _) = do
    let fv = M.keys gctx ++ M.keys ctx
    t <- typeOf gctx ctx e
    case t of
        Spi x exp r -> do
            case cmpTypes fv exp act of
                Just o | o /= LT -> Right ()
                _ -> let em s t = s <+> etext "(" <> (epretty $ reify fv t $ Stype maxBound) <> etext ") _ _"
                     in Left [emsgLC l' c' "" $ em (etext "Expected type: Id") exp $$
                        em (etext "But term" <+> epretty e2 <+> etext "has type Id") act]
            let x' = T.freshName x (M.keys gctx ++ M.keys ctx)
                r' = r $ liftValue [x'] (svar x') exp
            undefined {- if elem x' $ freeVars $ unNorm $ reify (x' : fv) r' (Stype maxBound)
                then Left [emsgLC l c "" $ etext "Expected arrow type" $$ etext "But term" <+>
                    epretty e <+> etext "has type" <+> epretty (reify fv t $ Stype maxBound)]
                else Right r' -}
        _ -> Left [emsgLC l c "" $ etext "Expected pi type" $$ etext "But term" <+> epretty e
                <+> etext "has type" <+> eprettyHead (reify fv t $ Stype maxBound)]
typeOfLam _ _ _ _ _ _ _ = error "typeOfLam"

hasType :: Ctx -> CtxT -> Expr -> Value -> EDocM ()
hasType gctx ctx (Lam _ [] e) ty = hasType gctx ctx e ty
hasType gctx ctx (Lam i (x:xs) e) (Spi z a b) =
    let (x',e') = renameExpr (M.keys gctx ++ M.keys ctx) (unBinder x) (Lam i xs e)
    in hasType gctx (M.insert x' a ctx) e' (b $ liftValue [x'] (svar x') a)
hasType gctx ctx (Lam _ (Binder (Arg (PIdent ((l,c),_))):_) _) ty =
    Left [emsgLC l c "" $ expType 1 (M.keys gctx ++ M.keys ctx) ty $$ etext "But lambda expression has pi type"]
hasType gctx ctx i@(Idp (PIdp ((l,c),_))) exp@(Spi x a _) =
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) exp (Spi x a $ \v -> Sid a v v) i
hasType gctx ctx (Idp (PIdp ((l,c),_))) ty =
    Left [emsgLC l c "" $ expType 1 (M.keys gctx ++ M.keys ctx) ty $$ etext "But idp has pi type"]
hasType gctx ctx i@(Pmap (Ppmap ((l,c),_)) e) exp@(Spi x (Sid t a b) r) =
    let x' = T.freshName x (M.keys gctx ++ M.keys ctx)
    in case r (liftValue [x'] (svar x') a) of
        Sid s _ _ -> do
            hasType gctx ctx e (sarr t s)
            let e' = evalOfType gctx e (sarr t s) 0 (ctxtToCtx ctx)
                act = Sid t a b `sarr` Sid s (app 0 e' a) (app 0 e' b)
            cmpTypesErr l c (M.keys gctx ++ M.keys ctx) exp act i
        _ -> Left [emsgLC l c "" $ expType 2 (M.keys gctx ++ M.keys ctx) exp $$
            etext "But pmap _ has type of the form x = y -> _ x = _ y"]
hasType gctx ctx (Pmap (Ppmap ((l,c),_)) _) exp@(Spi _ _ _) =
    Left [emsgLC l c "" $ expType 2 (M.keys gctx ++ M.keys ctx) exp $$
        etext "But pmap _ has type of the form x = y -> _ x = _ y"]
hasType gctx ctx (Pmap (Ppmap ((l,c),_)) _) exp =
    Left [emsgLC l c "" $ expType 1 (M.keys gctx ++ M.keys ctx) exp $$ etext "But pmap _ has pi type"]
hasType gctx ctx (Paren _ e) ty = hasType gctx ctx e ty
hasType gctx ctx e ty = do
    ty1 <- typeOf gctx ctx e
    let (l,c) = getPos e
    cmpTypesErr l c (M.keys gctx ++ M.keys ctx) ty ty1 e

evalDecl :: String -> Expr -> Maybe Expr -> StateT (Ctx,Ctx) EDocM (Value,Value)
evalDecl name expr mty = do
    (gctx,ctx) <- get
    let ctxt = ctxToCtxt ctx
    tv <- case mty of
        Nothing -> lift (typeOf gctx ctxt expr)
        Just ty -> do
            vty <- lift (typeOf gctx ctxt ty)
            let (l,c) = getPos ty
            lift $ cmpTypesErr l c (M.keys gctx ++ M.keys ctx) (Stype $ pred maxBound) vty ty
            return (eval gctx ty 0 ctx)
    lift (hasType gctx ctxt expr tv)
    let ev = evalOfType gctx expr tv 0 ctx
    put (M.insert name (ev,tv) gctx, M.delete name ctx)
    return (ev,tv)

eval :: Ctx -> Expr -> Integer -> Ctx -> Value
eval gctx (Let defs e) n ctx =
    let decls = either (error "eval.Let.1") id (processDefs defs)
        st = forM_ decls $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
        (gctx',ctx') = either (error "eval.Let.2") id $ execStateT st (gctx, ctx)
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
    Sid (either (const $ error "eval.Id") id $ typeOf gctx (ctxToCtxt ctx) a) (eval gctx a 0 ctx) (eval gctx b 0 ctx)
eval _ (Nat _) 0 _ = Snat
eval _ (Universe (U (_,t))) 0 _ = Stype (parseLevel t)
eval gctx (App e1 e2) n ctx = 
    let Right (Spi _ a _) = typeOf gctx (ctxToCtxt ctx) e1
    in app n (eval gctx e1 n ctx) (evalOfType gctx e2 a n ctx)
eval gctx (Var (Arg (PIdent (_,x)))) _ ctx =
    fst $ fromMaybe (error $ "eval: Unknown identifier " ++ x) $ M.lookup x ctx `mplus` M.lookup x gctx
eval _ (Suc _) _ _ = Slam "n" $ \_ _ -> Ssuc
eval _ (NatConst (PInt (_,x))) _ _ = genConst (read x :: Integer)
  where genConst 0 = Szero
        genConst n = Ssuc $ genConst (n - 1)
eval gctx (Rec _) _ ctx = Slam "P" $ \pk pm pv -> Slam "z" $ \zk zm zv -> Slam "s" $ \sk sm sv -> Slam "x" $ \xk xm ->
    rec (M.keys gctx ++ M.keys ctx) xk (action xm $ action sm $ action zm pv) (action xm $ action sm zv) (action xm sv)
eval gctx (Paren _ e) n ctx = eval gctx e n ctx

eval _ (Var (NoArg _)) _ _ = error "eval.NoArg"
eval _ (Lam _ _ _) _ _ = error "eval.Lam"
eval _ (Idp _) _ _ = error "eval.Idp"
eval _ (Pmap _ _) _ _ = error "eval.Pmap"
eval _ (Arr _ _) _ _ = error "eval.Arr > 0"
eval _ (Pi _ _) _ _ = error "eval.Pi > 0"
eval _ (Prod _ _) _ _ = error "eval.Prod > 0"
eval _ (Sigma _ _) _ _ = error "eval.Sigma > 0"
eval _ (Id _ _) _ _ = error "eval.Id > 0"
eval _ (Nat _) _ _ = error "eval.Nat > 0"
eval _ (Universe _) _ _ = error "eval.U > 0"

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
    let x' = Arg $ PIdent ((-1,-1), T.freshName x $ freeVars e)
    in evalOfType gctx (Lam (PLam i) [Binder x'] $ App pm $ Var x') t n ctx
evalOfType gctx (Paren _ e) ty n ctx = evalOfType gctx e ty n ctx
evalOfType gctx e _ n ctx = eval gctx e n ctx

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) = f n []
app n _ = error "app"

infixl 5 `aApp`
aApp = App

rec :: [String] -> Integer -> Value -> Value -> Value -> Value -> Value
rec ctx n p z s = go
  where
    go Szero = z
    go (Ssuc x) = app n (app n s x) (go x)
    go t@(Ne e) = undefined
        {- let r = Rec (PR (getPos e,"R"))
                `aApp` unNorm (reify ctx p $ Snat `sarr` Stype maxBound)
                `aApp` unNorm (reify ctx z $ app n p Szero)
                `aApp` unNorm (reify ctx s $ Spi "x" Snat $ \x -> app n p x `sarr` app n p (Ssuc x))
                `aApp` e
        in liftValue (freeVars r) (Ne r) (app n p t) -}
    go _ = error "rec.go"

cmpTypes :: [String] -> Value -> Value -> Maybe Ordering
cmpTypes ctx (Spi x a b) (Spi _ a' b') = case (cmpTypes ctx a' a, cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = T.freshName x ctx
          ctx' = fresh:ctx
cmpTypes ctx (Ssigma x a b) (Ssigma _ a' b') = case (cmpTypes ctx a a', cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = T.freshName x ctx
          ctx' = fresh:ctx
cmpTypes ctx (Sid t a b) (Sid t' a' b') = case cmpTypes ctx t t' of
    Nothing -> Nothing
    Just GT -> if cmpValues ctx a a' t  && cmpValues ctx b b' t  then Just EQ else Nothing
    _       -> if cmpValues ctx a a' t' && cmpValues ctx b b' t' then Just EQ else Nothing
cmpTypes _ Snat Snat = Just EQ
cmpTypes _ (Stype k) (Stype k') = Just (compare k k')
cmpTypes _ (Ne t) (Ne t') = if t == t' then Just EQ else Nothing
cmpTypes _ _ _ = Nothing

cmpTypesErr :: Int -> Int -> [String] -> Value -> Value -> Expr -> EDocM ()
cmpTypesErr l c ctx t1 t2 e = case cmpTypes ctx t1 t2 of
    Just o | o /= LT -> Right ()
    _ -> Left [emsgLC l c "" $ expType (-1) ctx t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> epretty (reify ctx t2 $ Stype maxBound)]

cmpValues :: [String] -> Value -> Value -> Value -> Bool
cmpValues ctx e1 e2 t = reify ctx e1 t == reify ctx e2 t

liftValue :: [String] -> Value -> Value -> Value
liftValue _ e@(Slam _ _) (Spi _ _ _) = e
liftValue fv e@(Ne _) (Spi x a _) = Slam x $ \k m v ->
    let Ne e' = action m e
    in Ne $ T.App e' (reify fv v a)
liftValue _ t _ = t

reify :: [String] -> Value -> Value -> T.Term
reify ctx (Slam x f) (Spi _ a b) =
    let x' = T.freshName x ctx
    in T.Lam [x'] $ reify (x':ctx) (f 0 [] $ liftValue [x'] (svar x') a) $ b (svar x')
reify _ Szero Snat = T.NatConst 0
reify ctx Szero (Sid t _ _) = T.App T.Idp (reify ctx Szero t)
reify ctx (Ssuc e) Snat = case reify ctx e Snat of
    T.NatConst n -> T.NatConst (n + 1)
    t -> T.App T.Suc t
reify ctx e@(Ssuc _) (Sid t _ _) = T.App T.Idp (reify ctx e t)
reify ctx (Spi x a b) (Stype l) =
    let x' = T.freshName x ctx
        bnd = [([x'], reify ctx a $ Stype l)]
    in T.Pi bnd $ reify (x':ctx) (b $ svar x') (Stype l)
reify ctx (Ssigma x a b) (Stype l) =
    let x' = T.freshName x ctx
        bnd = [([x'], reify ctx a $ Stype l)]
    in T.Sigma bnd $ reify (x':ctx) (b $ svar x') (Stype l)
reify ctx (Sid t a b) (Stype _) = T.Id (reify ctx a t) (reify ctx b t)
reify _ (Stype l) (Stype _) = T.Universe l
reify _ Snat (Stype _) = T.Nat
reify ctx (Sidp x) (Sid t _ _) = T.App T.Idp (reify ctx x t)
reify _ (Ne e) _ = e

reify _ (Slam _ _) (Ssigma _ _ _) = error "reify.Slam.Ssigma"
reify _ (Slam _ _) Snat = error "reify.Slam.Snat"
reify _ (Slam _ _) (Sid _ _ _) = error "reify.Slam.Sid"
reify _ (Slam _ _) (Stype _) = error "reify.Slam.Stype"
reify _ (Slam _ _) (Ne _) = error "reify.Slam.Ne"
reify _ (Slam _ _) _ = error "reify.Slam"
reify _ Szero (Spi _ _ _) = error "reify.Szero.Spi"
reify _ Szero (Ssigma _ _ _) = error "reify.Szero.Ssigma"
reify _ Szero (Stype _) = error "reify.Szero.Stype"
reify _ Szero (Ne _) = error "reify.Szero.Ne"
reify _ Szero _ = error "reify.Szero"
reify _ (Ssuc _) (Spi _ _ _) = error "reify.Ssuc.Spi"
reify _ (Ssuc _) (Ssigma _ _ _) = error "reify.Ssuc.Ssigma"
reify _ (Ssuc _) (Stype _) = error "reify.Ssuc.Stype"
reify _ (Ssuc _) (Ne _) = error "reify.Ssuc.Ne"
reify _ (Ssuc _) _ = error "reify.Ssuc"
reify _ (Spi _ _ _) _ = error "reify.Spi"
reify _ (Ssigma _ _ _) _ = error "reify.Ssigma"
reify _ Snat _ = error "reify.Snat"
reify _ (Sid _ _ _) _ = error "reify.Sid"
reify _ (Stype _) _ = error "reify.Stype"
reify _ (Sidp _) (Spi _ _ _) = error "reify.Sidp.Spi"
reify _ (Sidp _) (Ssigma _ _ _) = error "reify.Sidp.Ssigma"
reify _ (Sidp _) Snat = error "reify.Sidp.Snat"
reify _ (Sidp _) (Stype _) = error "reify.Sidp.Stype"
reify _ (Sidp _) (Ne _) = error "reify.Sidp.Ne"
reify _ (Sidp _) _ = error "reify.Sidp"
