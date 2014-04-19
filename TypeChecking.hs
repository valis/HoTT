module TypeChecking
    ( typeCheck
    , processDefs
    ) where

import qualified Data.Map as M

import ErrorDoc
import Value
import Parser.AbsGrammar
import Syntax.Common
import Syntax.Raw
import qualified Syntax.Term as T
import Eval
import TCM
import TypeInference

maxType :: Expr -> Expr -> Value -> Value -> TCM Value
maxType _ _ (Stype k1) (Stype k2) = return $ Stype (max k1 k2)
maxType e1 e2 t1 t2 = liftTCM2 (error "maxType")
    (cmpTypesErr (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr (Stype $ pred maxBound) t2 e2)

isType :: Expr -> TCM T.Term
isType e = do
    r <- typeCheck e Nothing
    t <- typeOf r
    cmpTypesErr (Stype $ pred maxBound) t e
    return r

processDefs :: [Def] -> [(String,Maybe Expr,[Arg],Expr)]
processDefs [] = []
processDefs (DefType _ t : Def (PIdent (_,name)) args e : defs) = (name,Just t,args,e) : processDefs defs
processDefs (Def (PIdent (_,name)) args e : defs) = (name,Nothing,args,e) : processDefs defs
processDefs _ = error "processDefs"

evalTCM :: T.Term -> TCM Value
evalTCM e = do
    ctx <- askCtx
    return $ eval 0 (ctxToCtxV ctx) e

typeCheck'depType :: ([([String],T.Term)] -> T.Term -> T.Term) -> TypedVar -> Expr -> TCM T.Term
typeCheck'depType dt (TypedVar _ vars t) e = case exprToVars vars of
    Right vars' -> do
        tr <- isType t
        t' <- evalTCM tr
        r <- updateCtx t' vars'
        fmap (dt [(map unArg vars', tr)]) $ local (\_ _ _ _ -> r) (isType e)
    Left lc -> errorTCM $ emsgLC lc "Expected identifier" enull

updateCtx :: Value -> [Arg] -> TCM (T.DBIndex, [String], M.Map String T.DBIndex, Ctx)
updateCtx _ [] = ask
updateCtx tv (NoArg _ : as) =
    local (\i c mctx (gctx,lctx) -> (i + 1, "_" : c, mctx, (gctx, (svar i 0 tv, tv) : lctx))) (updateCtx tv as)
updateCtx tv (Arg (PIdent (_,x)) : as) =
    local (\i c mctx (gctx,lctx) -> (i + 1, x : c, M.insert x i mctx, (gctx, (svar i 0 tv, tv) : lctx))) (updateCtx tv as)

exprToVars :: Expr -> Either (Int,Int) [Arg]
exprToVars = fmap reverse . go
  where
    go (Var a) = Right [a]
    go (App as (Var a)) = fmap (a :) (go as)
    go e = Left (getPos e)

evalDecl :: String -> Expr -> Maybe Expr -> (T.Term -> Maybe T.Term -> TCM a) -> TCM a
evalDecl name expr mty a = do
    (er,tr,tv) <- case mty of
        Nothing -> do
            er <- typeCheck expr Nothing
            tv <- typeOf er
            return (er, Nothing, tv)
        Just ty -> do
            tr <- typeCheck ty Nothing
            tv <- evalTCM tr
            er <- typeCheck expr (Just tv)
            return (er, Just tr, tv)
    ev <- evalTCM er
    local (\i c mctx (gctx, lctx) -> (i + 1, name : c, M.insert name i mctx, (gctx, (ev,tv) : lctx))) (a er tr)

typeCheck :: Expr -> Maybe Value -> TCM T.Term
typeCheck (Let defs e) h = do
    defs' <- liftEDocM (preprocessDefs defs)
    go (processDefs defs') [] (typeCheck e h)
  where
    go [] l e = fmap (T.Let $ reverse l) e
    go ((name,ty,args,expr):ds) l e =
        let p = if null args then getPos expr else argGetPos (head args)
        in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty $ \er mtr ->
            go ds (T.Def name (fmap (\tr -> (tr, map unArg args)) mtr) er : l) e
typeCheck (Paren _ e) h = typeCheck e h
typeCheck (Lam _ [] e) h = typeCheck e h

typeCheck (Lam _ (x:xs) e) (Just (Spi a b)) = do
    i <- askIndex
    let p = if null xs then getPos e else binderGetPos (head xs)
        v = svar i 0 a
        x' = unBinder x
    fmap (T.Lam 0 [x']) $ local (\i c mctx (gctx,lctx) -> (i + 1, x' : c, M.insert x' i mctx, (gctx, (v,a) : lctx))) $
        typeCheck (Lam (PLam (p,"\\")) xs e) $ Just (app 0 b v)
typeCheck (Lam _ (Binder arg : _) _) (Just ty) = do
    let lc = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But lambda expression has pi type"
typeCheck j@(Idp _) (Just exp@(Spi a (Slam x _))) = do
    let ctx = (M.singleton (freshName "a" [x]) a, [])
    cmpTypesErr exp (eval 0 ctx $ T.Pi 0 [([x],T.Var "a")] $ T.Id 0 (T.Var "a") (T.LVar 0) (T.LVar 0)) j
    return T.Idp
typeCheck (Idp (PIdp (lc,_))) (Just ty) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But idp has pi type"
typeCheck e@(Coe (PCoe (lc,_))) (Just ty@(Spi a@(Sid (Stype _) x y) b)) = do
    i <- askIndex
    case app 0 b $ svar i 0 a of
        Spi x' y' | cmpTypes i 0 x x' && cmpTypes (i + 1) 0 y (app 0 y' $ svar i 0 x') -> return T.Coe
        _ -> coeErrorMsg lc ty
typeCheck (Coe (PCoe (lc,_))) (Just ty) = coeErrorMsg lc ty
typeCheck ea@(App e1 e) (Just exp@(Sid t a b)) | Idp _ <- dropParens e1 = do
    r <- typeCheck e (Just t)
    e' <- evalTCM r
    cmpTypesErr exp (Sid t e' e') ea
    return (T.App 0 T.Idp r)
typeCheck (App e1 _) (Just exp) | Idp (PIdp (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 exp $$ etext "But idp _ has Id type"
typeCheck (Pair e1 e2) (Just (Ssigma a b)) = do
    r1 <- typeCheck e1 (Just a)
    v1 <- evalTCM r1
    r2 <- typeCheck e2 $ Just (app 0 b v1)
    return (T.Pair r1 r2)
typeCheck e@(Pair _ _) (Just exp) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos e) "" $ expType i c (-1) exp $$ etext "But term" <+> eprettyExpr e <+> etext "has Sigma type"
typeCheck (Proj1 (PProjl (lc,_))) (Just r@(Spi a'@(Ssigma a _) b)) = do
    i <- askIndex
    case isArr i a' b of
        Just b' | cmpTypes i 0 a b' -> return T.Proj1
        _ -> proj1ErrorMsg lc r
typeCheck (Proj1 (PProjl (lc,_))) (Just exp) = proj1ErrorMsg lc exp
-- proj2 : (p : (x : A) -> B x) -> B (proj1 p)
typeCheck (Proj2 (PProjr (lc,_))) (Just r@(Spi a'@(Ssigma a b) b')) = do
    i <- askIndex
    if cmpTypes (i + 1) 0 (app 0 b $ reflect 0 (\l -> T.App 0 T.Proj1 $ T.LVar $ l - i - 1) a) (app 0 b' $ svar i 0 a')
        then return T.Proj2
        else proj2ErrorMsg lc r
typeCheck (Proj2 (PProjr (lc,_))) (Just exp) = proj2ErrorMsg lc exp
typeCheck e (Just exp) = do
    r <- typeCheck e Nothing
    act <- typeOf r
    cmpTypesErr exp act e
    return r

typeCheck (Pair e1 e2) Nothing = liftTCM2' T.Pair (typeCheck e1 Nothing) (typeCheck e2 Nothing)
typeCheck (Lam (PLam (lc,_)) _ _) Nothing = inferErrorMsg lc "the argument"
typeCheck (Idp (PIdp (lc,_))) Nothing = inferErrorMsg lc "idp"
typeCheck (Coe (PCoe (lc,_))) Nothing = inferErrorMsg lc "coe"
typeCheck (App e1 e) Nothing | Idp _ <- dropParens e1 = fmap (T.App 0 T.Idp) (typeCheck e Nothing)
typeCheck (Proj1 (PProjl (lc,_))) Nothing = inferErrorMsg lc "proj1"
typeCheck (Proj2 (PProjr (lc,_))) Nothing = inferErrorMsg lc "proj2"
typeCheck (App e1 e) Nothing | Proj1 _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Ssigma a _ -> return (T.App 0 T.Proj1 r)
        _ -> expTypeBut "Sigma" e t
typeCheck (App e1 e) Nothing | Proj2 (PProjr p) <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Ssigma a b -> return (T.App 0 T.Proj2 r)
        _ -> expTypeBut "Sigma" e t
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeCheck (Pmap e1 e2) Nothing = do
    (r1,r2) <- liftTCM2' (,) (typeCheck e1 Nothing) (typeCheck e2 Nothing)
    t1 <- typeOf r1
    t2 <- typeOf r2
    case (t1,t2) of
        (Sid (Spi a b) f g, Sid a' x y) -> do
            (i,c,mctx,ctx) <- ask
            if cmpTypes i 1 a' a
                then return (T.Pmap r1 r2)
                else pmapErrMsg e2 a' (eprettyType i c a)
        (Sid t f g, Sid a' x y) -> pmapErrMsg e1 t (etext "_ -> _")
        (Sid t f g, _) -> expTypeBut "Id" e2 t2
        _ -> expTypeBut "Id" e1 t1
typeCheck (App e1 e) Nothing | Coe _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Sid (Stype _) x y -> return (T.App 0 T.Coe r)
        _ -> expTypeBut "Id Type _ _" e t
typeCheck (Arr e1 e2) Nothing = do
    (r1,r2) <- liftTCM2' (,) (isType e1) (isType e2)
    return (T.Pi 0 [([],r1)] r2)
typeCheck (Prod e1 e2) Nothing = do
    (r1,r2) <- liftTCM2' (,) (isType e1) (isType e2)
    return (T.Sigma 0 [([],r1)] r2)
typeCheck (Pi [] e) Nothing = typeCheck e Nothing
typeCheck (Pi (t:tv) e) Nothing = typeCheck'depType (T.Pi 0) t (Pi tv e)
typeCheck (Sigma [] e) Nothing = typeCheck e Nothing
typeCheck (Sigma (t:tv) e) Nothing = typeCheck'depType (T.Sigma 0) t (Sigma tv e)
typeCheck (Id e1 e2) Nothing = do
    r1 <- typeCheck e1 Nothing
    t <- typeOf r1
    r2 <- typeCheck e2 (Just t)
    i <- askIndex
    return $ T.Id 0 (reifyType i 0 t) r1 r2
typeCheck (Over t1 t) Nothing | Id e1 e2 <- dropParens t1 = do
    r <- typeCheck t Nothing
    v <- evalTCM r
    (r1,r2) <- liftTCM2' (,) (typeCheck e1 $ Just v) (typeCheck e2 $ Just v)
    return (T.Id 0 r r1 r2)
typeCheck (Over t _) Nothing = errorTCM $ emsgLC (getPos t) "Expected term of the form _ = _" enull
typeCheck (Nat _) Nothing = return T.Nat
typeCheck (Universe (U (_,t))) Nothing = return $ T.Universe (parseLevel t)
typeCheck (App e1 e2) Nothing = do
    r1 <- typeCheck e1 Nothing
    t1 <- typeOf r1
    case t1 of
        Spi a b -> fmap (T.App 0 r1) $ typeCheck e2 (Just a)
        _ -> expTypeBut "pi" e1 t1
typeCheck (Var (NoArg (Pus (lc,_)))) Nothing = errorTCM $ emsgLC lc "Expected identifier" enull
typeCheck (Var (Arg (PIdent (lc,x)))) Nothing = do
    (i,_,mctx,(gctx,_)) <- ask
    case (M.lookup x mctx, M.lookup x gctx) of
        (Nothing, Nothing) -> errorTCM $ emsgLC lc ("Unknown identifier " ++ x) enull
        (Nothing, Just _) -> return (T.Var x)
        (Just l, _) -> return $ T.LVar (i - l - 1)
typeCheck (Suc _) Nothing = return T.Suc
typeCheck (NatConst (PInt (_,x))) Nothing = return $ T.NatConst (read x)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeCheck (Rec _) Nothing = return T.Rec
{-
typeCheck (Iso _) Nothing =
    let term = T.Pi [(["A"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [(["B"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [(["f"],T.Pi [([],T.LVar 1)] $ T.LVar 0)] $
               T.Pi [(["g"],T.Pi [([],T.LVar 1)] $ T.LVar 2)] $
               T.Pi [([],T.Pi [(["a"],T.LVar 3)] $
                    T.Id (T.LVar 4) (T.LVar 1 `T.App` (T.LVar 2 `T.App` T.LVar 0)) (T.LVar 0))] $
               T.Pi [([],T.Pi [(["b"],T.LVar 2)] $
                    T.Id (T.LVar 3) (T.LVar 2 `T.App` (T.LVar 1 `T.App` T.LVar 0)) (T.LVar 0))] $
               T.Id (T.Universe $ pred $ pred maxBound) (T.LVar 3) (T.LVar 2)
    in return (eval 0 (M.empty,[]) term)
-}

isArr :: T.DBIndex -> Value -> Value -> Maybe Value
isArr i t f =
    let r = app 0 f (svar i 0 t)
    in if isFreeVar 0 (i + 1) r then Nothing else Just r

eprettyType :: T.DBIndex -> [String] -> Value -> EDoc
eprettyType i c t = epretty c $ T.simplify (reifyType i 0 t)

inferErrorMsg :: (Int,Int) -> String -> TCM a
inferErrorMsg lc s = errorTCM $ emsgLC lc ("Cannot infer type of " ++ s) enull

pmapErrMsg :: Expr -> Value -> EDoc -> TCM a
pmapErrMsg expr ty j = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos expr) "" $ etext "Expected type of the form _ = _ |" <+> j $$
        etext "But term" <+> eprettyExpr expr <+> etext "has type _ = _ |" <+> eprettyType i c ty

coeErrorMsg :: (Int,Int) -> Value -> TCM a
coeErrorMsg lc ty = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But coe has type of the form Id Type A B -> A -> B"

pmapErrorMsg :: (Int,Int) -> Value -> TCM a
pmapErrorMsg lc ty = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) ty $$ etext ("But pmap has type of the form "
        ++ "Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)")

pmap1ErrorMsg :: (Int,Int) -> Value -> TCM a
pmap1ErrorMsg lc ty = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) ty $$
        etext "But pmap _ has type of the form (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)"

proj1ErrorMsg :: (Int,Int) -> Value -> TCM a
proj1ErrorMsg lc exp = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But proj1 has type of the form ((a : A) -> B a) -> A"

proj2ErrorMsg :: (Int,Int) -> Value -> TCM a
proj2ErrorMsg lc exp = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
        etext "But proj2 has type of the form (p : (a : A) -> B a) -> B (proj1 p)"

extErrorMsg :: (Int,Int) -> Value -> TCM a
extErrorMsg lc exp = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
        etext ("But ext has type either of the form ((x : A) -> f x = g x) -> f = g or "
        ++ "of the form (s : Id A a a') * Id (B a') (trans B s b) b' -> Id ((a : A) * B a) (a,b) (a',b')")

expType :: T.DBIndex -> [String] -> Int -> Value -> EDoc
expType i c l ty = etext "Expected type:" <+> eprettyLevel c l (T.simplify $ reifyType i 0 ty)

cmpTypesErr :: Value -> Value -> Expr -> TCM ()
cmpTypesErr t1 t2 e = do
    (i,c,_,_) <- ask
    if cmpTypes i 0 t2 t1
        then return ()
        else errorTCM $ emsgLC (getPos e) "" $ expType i c (-1) t1 $$
            etext "But term" <+> eprettyExpr e <+> etext "has type" <+> eprettyType i c t2

expTypeBut :: String -> Expr -> Value -> TCM a
expTypeBut exp e act = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos e) "" $ etext ("Expected " ++ exp ++ " type") $$
        etext "But term" <+> eprettyExpr e <+> etext "has type" <+> eprettyHead c (T.simplify $ reifyType i 0 act)
