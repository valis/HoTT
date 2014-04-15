module TypeChecking
    ( typeCheck
    , evalDecl, processDefs
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
    local (\i c mctx (gctx,lctx) -> (i + 1, "_" : c, mctx, (gctx, (svar i tv, tv) : lctx))) (updateCtx tv as)
updateCtx tv (Arg (PIdent (_,x)) : as) =
    local (\i c mctx (gctx,lctx) -> (i + 1, x : c, M.insert x i mctx, (gctx, (svar i tv, tv) : lctx))) (updateCtx tv as)

exprToVars :: Expr -> Either (Int,Int) [Arg]
exprToVars = fmap reverse . go
  where
    go (Var a) = Right [a]
    go (App as (Var a)) = fmap (a :) (go as)
    go e = Left (getPos e)

typeCheck :: Expr -> Maybe Value -> TCM T.Term
typeCheck (Let defs e) h = do
    defs' <- liftEDocM (preprocessDefs defs)
    (mctx,ctx) <- go (processDefs defs')
    local (\i c _ _ -> (i,c,mctx,ctx)) (typeCheck e h)
  where
    go [] = fmap (\(_,_,mctx,ctx) -> (mctx,ctx)) ask
    go ((name,ty,args,expr):ds) = do
        let p = if null args then getPos expr else argGetPos (head args)
        (mctx',ctx',_,_) <- evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
        local (\i c _ _ -> (i,c,mctx',ctx')) (go ds)
typeCheck (Paren _ e) h = typeCheck e h
typeCheck (Lam _ [] e) h = typeCheck e h

typeCheck (Lam _ (x:xs) e) (Just (Spi 0 z a b)) = do
    i <- askIndex
    let p = if null xs then getPos e else binderGetPos (head xs)
        v = svar i a
        x' = unBinder x
    fmap (T.Lam [x']) $ local (\i c mctx (gctx,lctx) -> (i + 1, x' : c, M.insert x' i mctx, (gctx, (v,a) : lctx))) $
        typeCheck (Lam (PLam (p,"\\")) xs e) $ Just (b 0 [] v)
typeCheck (Lam _ (Binder arg : _) _) (Just ty) = do
    let lc = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But lambda expression has pi type"
typeCheck j@(Idp _) (Just exp@(Spi 0 x a _)) = do
    let ctx = (M.singleton (freshName "a" [x]) a, [])
    cmpTypesErr exp (eval 0 ctx $ T.Pi [([x],T.Var "a")] $ T.Id (T.Var "a") (T.LVar 0) (T.LVar 0)) j
    return T.Idp
typeCheck (Idp (PIdp (lc,_))) (Just ty) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But idp has pi type"
typeCheck e@(Coe (PCoe (lc,_))) (Just ty@(Spi 0 v a@(Sid 0 (Stype _) x y) b)) = do
    i <- askIndex
    case b 0 [] $ svar i a of
        Spi 0 v' x' y' | cmpTypes i x x' && cmpTypes (i + 1) y (y' 0 [] $ svar i x') -> return T.Coe
        _ -> coeErrorMsg lc ty
typeCheck (Coe (PCoe (lc,_))) (Just ty) = coeErrorMsg lc ty
typeCheck ea@(App e1 e) (Just exp@(Sid 0 t a b)) | Idp _ <- dropParens e1 = do
    r <- typeCheck e (Just t)
    e' <- evalTCM r
    cmpTypesErr exp (Sid 0 t e' e') ea
    return (T.App T.Idp r)
typeCheck (App e1 _) (Just exp) | Idp (PIdp (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 exp $$ etext "But idp _ has Id type"
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeCheck e@(Pmap (Ppmap (lc,_))) (Just exp@(Spi 0 v a@(Sid 0 (Spi 0 v' a' b') f g) b)) = do
    i <- askIndex
    case isArr i a b of
        Just (Spi 0 v2 a2'@(Sid 0 a2 x y) b2') | cmpTypes i a2 a' -> do
            let ctx' = [("a",a),("a'",a'),("x",x),("y",y),("B",Slam v' b'),("f'",app 0 f x),("g'",app 0 g y)]
                term = T.Pi [([],T.Var "a")] $ T.Pi [(["p"],T.Id (T.Var "a'") (T.Var "x") (T.Var "y"))] $
                    T.Id (T.Var "B" `T.App` T.Var "y")
                         (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.LVar 0) `T.App` T.Var "f'")
                         (T.Var "g'")
            cmpTypesErr exp (eval 0 (M.fromList ctx', []) term) e
            return T.Pmap
        _ -> pmapErrorMsg lc exp
typeCheck (Pmap (Ppmap (lc,_))) (Just exp) = pmapErrorMsg lc exp
typeCheck ea@(App e1 e) (Just ty@(Spi 0 v a'@(Sid 0 a x y) b')) | Pmap _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    (i,c,_,_) <- ask
    case t of
        Sid 0 (Spi 0 v1 a1 b1) f g | cmpTypes i a a1 -> do
            let ctx' = [("a'",a'),("B",Slam v1 b1),("y",y),("f'",app 0 f x),("g'",app 0 g y)]
                term = T.Pi [(["p"],T.Var "a'")] $ T.Id (T.Var "B" `T.App` T.Var "y")
                    (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.LVar 0) `T.App` T.Var "f'")
                    (T.Var "g'")
            cmpTypesErr ty (eval 0 (M.fromList ctx', []) term) ea
            return (T.App T.Pmap r)
        _ -> errorTCM $ emsgLC (getPos e) "" $
            etext "Expected type: _ = _ |" <+> epretty c (T.Pi [([],reifyType i a)] $ T.Var "_") $$
            etext "But term" <+> eprettyExpr e <+> etext "has type" <+> epretty c (reifyType i t)
typeCheck (App e1 e) (Just ty) | Pmap (Ppmap (lc,_)) <- dropParens e1 = pmap1ErrorMsg lc ty
{- TODO
typeCheck (Ext (PExt (lc,_))) (Just ty@(Spi 0 x' s@(Spi 0 _ a' b') t)) = do
    i <- askIndex
    case isArr i s t of
        Just (Sid 0 (Spi 0 _ a b) f g) | cmpTypes i a a' ->
            let v = svar i a
            in if cmpTypes (i + 1) (b' 0 [] v) (Sid 0 (b 0 [] v) (app 0 f v) (app 0 g v))
                then return ty
                else extErrorMsg lc ty
        _ -> extErrorMsg lc ty
-- ext : (s : Id A x x') * Id (B x') (trans B s y) y' -> Id ((x : A) * B x) (x,y) (x',y')
--       a'              * b'                         -> Id (a       * b  ) p     q
typeCheck (Ext (PExt (lc,_))) (Just ty@(Spi 0 x' s@(Ssigma 0 _ a' b') t)) = do
    i <- askIndex
    case isArr i s t of
        Just (Sid 0 (Ssigma 0 x a b) p q) ->
            let v = svar i $ Sid 0 a (proj1 p) (proj1 q)
            in if cmpTypes i a' (Sid 0 a (proj1 p) (proj1 q)) &&
                  cmpTypes (i + 1) (b' 0 [] v) (Sid 0 (b 0 [] $ proj1 q) (trans 0 (Slam x b) s $ proj2 p) (proj2 q))
               then return ty
               else extErrorMsg lc ty
        _ -> extErrorMsg lc ty
typeCheck (Ext (PExt (lc,_))) (Just ty) = extErrorMsg lc ty
typeCheck (App e1 e) (Just r@(Sid 0 (Spi 0 x a b) f g)) | Ext _ <- dropParens e1 = do
    typeOfH e $ T $ Spi 0 x a $ \k m v -> Sid 0 (b k m v) (app k (action m f) v) (app k (action m g) v)
    return r
-- (s : Id a (proj1 p) (proj1 q)) * (Id (B (proj1 q)) (trans B s (proj2 p)) (proj2 q))
typeCheck (App e1 e) (Just r@(Sid 0 (Ssigma 0 x a b) p q)) | Ext _ <- dropParens e1 = do
    typeOfH e $ T $ Ssigma 0 x (Sid 0 a (proj1 p) (proj1 q)) $ \k m s ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x b) s $ action m (proj2 p)
            r3 = action m (proj2 q)
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)], []) $ T.Id (T.Var "r1") (T.Var "r2") (T.Var "r3")
    return r
-}
typeCheck (App e1 e) (Just exp) | Ext (PExt (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
        etext "But term ext _ has type either of the form Id ((x : A) -> B x) _ _ or of the form Id ((x : A) * B x) _ _"
typeCheck (App e1 e) (Just (Sid 0 t x y)) | Inv _ <- dropParens e1 = do
    r <- typeCheck e $ Just (Sid 0 t y x)
    return (T.App T.Inv r)
typeCheck (App e1 e) (Just exp) | Inv (PInv (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But term inv _ has Id type"
typeCheck (Pair e1 e2) (Just (Ssigma 0 _ a b)) = do
    r1 <- typeCheck e1 (Just a)
    v1 <- evalTCM r1
    r2 <- typeCheck e2 $ Just (b 0 [] v1)
    return (T.Pair r1 r2)
typeCheck e@(Pair _ _) (Just exp) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos e) "" $ expType i c (-1) exp $$ etext "But term" <+> eprettyExpr e <+> etext "has Sigma type"
typeCheck (Proj1 (PProjl (lc,_))) (Just r@(Spi 0 x a'@(Ssigma 0 _ a _) b)) = do
    i <- askIndex
    case isArr i a' b of
        Just b' | cmpTypes i a b' -> return T.Proj1
        _ -> proj1ErrorMsg lc r
typeCheck (Proj1 (PProjl (lc,_))) (Just exp) = proj1ErrorMsg lc exp
-- proj2 : (p : (x : A) -> B x) -> B (proj1 p)
typeCheck (Proj2 (PProjr (lc,_))) (Just r@(Spi 0 x a'@(Ssigma 0 _ a b) b')) = do
    i <- askIndex
    if cmpTypes (i + 1) (b 0 [] $ reflect (\l -> T.App T.Proj1 $ T.LVar $ l - i - 1) a) (b' 0 [] $ svar i a')
        then return T.Proj2
        else proj2ErrorMsg lc r
typeCheck (Proj2 (PProjr (lc,_))) (Just exp) = proj2ErrorMsg lc exp
typeCheck (Comp (PComp (lc,_))) (Just exp) = do
    (i,c,_,_) <- ask
    case exp of
        Spi 0 v1 a1@(Sid 0 t1 x1 y1) b1
            | Just (Spi 0 v2 a2@(Sid 0 t2 x2 y2) b2) <- isArr i a1 b1, Just (Sid 0 t3 x3 y3) <- isArr i a2 b2
            , cmpTypes i t1 t2 && cmpTypes i t2 t3 && cmpValues i y1 x2 t1 && cmpValues i x1 x3 t1 && cmpValues i y2 y3 t2
            -> return T.Comp
        _ -> errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
                etext "But comp has type of the form Id A x y -> Id A y z -> Id A x z"
typeCheck (Inv (PInv (lc,_))) (Just exp) = do
    (i,c,_,_) <- ask
    case exp of
        Spi 0 v a@(Sid 0 t x y) b
            | Just (Sid 0 t' x' y') <- isArr i a b, cmpTypes i t t' && cmpValues i x y' t && cmpValues i x' y t
            -> return T.Inv
        _ -> errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But inv has type of the form Id A x y -> Id A y x"
-- invIdp : (p : Id t x y) -> Id (Id (Id t x y) p p) (comp (inv p) p) (idp p)
typeCheck e@(InvIdp _) (Just exp@(Spi 0 v a@(Sid 0 t x y) b)) = do
    let ctx' = (M.fromList [("a",a)], [])
        term = T.Pi [(["p"],T.Var "a")] $ T.Id
            (T.Id (T.Var "a") (T.LVar 0) (T.LVar 0))
            (T.Comp `T.App` (T.Inv `T.App` T.LVar 0) `T.App` T.LVar 0)
            (T.Idp `T.App` T.LVar 0)
    cmpTypesErr exp (eval 0 ctx' term) e
    return T.InvIdp
typeCheck (InvIdp (PInvIdp (lc,_))) (Just exp) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But invIdp has type of the form Id A x y -> _"
typeCheck e (Just exp) = do
    r <- typeCheck e Nothing
    act <- typeOf r
    cmpTypesErr exp act e
    return r

typeCheck (Pair e1 e2) Nothing = liftTCM2' T.Pair (typeCheck e1 Nothing) (typeCheck e2 Nothing)
typeCheck (Lam (PLam (lc,_)) _ _) Nothing = inferErrorMsg lc "the argument"
typeCheck (Idp (PIdp (lc,_))) Nothing = inferErrorMsg lc "idp"
typeCheck (Coe (PCoe (lc,_))) Nothing = inferErrorMsg lc "coe"
typeCheck (App e1 e) Nothing | Idp _ <- dropParens e1 = fmap (T.App T.Idp) (typeCheck e Nothing)
typeCheck (Pmap (Ppmap (lc,_))) Nothing = inferErrorMsg lc "pmap"
typeCheck (Ext (PExt (lc,_))) Nothing = inferErrorMsg lc "ext"
typeCheck (Proj1 (PProjl (lc,_))) Nothing = inferErrorMsg lc "proj1"
typeCheck (Proj2 (PProjr (lc,_))) Nothing = inferErrorMsg lc "proj2"
typeCheck (App e1 e) Nothing | Proj1 _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Ssigma 0 _ a _ -> return (T.App T.Proj1 r)
        _ -> expTypeBut "Sigma" e t
typeCheck (App e1 e) Nothing | Proj2 (PProjr p) <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Ssigma 0 _ a b -> return (T.App T.Proj2 r)
        _ -> expTypeBut "Sigma" e t
typeCheck (App e1 _) Nothing | Pmap (Ppmap (lc,_)) <- dropParens e1 = inferErrorMsg lc "pmap"
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeCheck (App e1' e2) Nothing | App e3 e1 <- dropParens e1', Pmap _ <- dropParens e3 = do
    (r1,r2) <- liftTCM2' (,) (typeCheck e1 Nothing) (typeCheck e2 Nothing)
    t1 <- typeOf r1
    t2 <- typeOf r2
    case (t1,t2) of
        (Sid 0 (Spi 0 v a b) f g, Sid 0 a' x y) -> do
            (i,c,mctx,ctx) <- ask
            if cmpTypes i a' a
                then return $ T.Pmap `T.App` r1 `T.App` r2
                else pmapErrMsg e2 a' (eprettyType i c a)
        (Sid 0 t f g, Sid 0 a' x y) -> pmapErrMsg e1 t (etext "_ -> _")
        (Sid 0 t f g, _) -> expTypeBut "Id" e2 t2
        _ -> expTypeBut "Id" e1 t1
typeCheck (App e1 e) Nothing | Coe _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Sid 0 (Stype _) x y -> return (T.App T.Coe r)
        _ -> expTypeBut "Id Type _ _" e t
typeCheck (App e1 e) Nothing | Inv _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Sid 0 t' x y -> return (T.App T.Inv r)
        _ -> expTypeBut "Id" e t
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeCheck (App e1 e) Nothing | InvIdp _ <- dropParens e1 = do
    r <- typeCheck e Nothing
    t <- typeOf r
    case t of
        Sid 0 _ _ _ -> return (T.App T.InvIdp r)
        _ -> expTypeBut "Id" e t
typeCheck (App e1' e2) Nothing | App e3 e1 <- dropParens e1', Comp (PComp (lc,_)) <- dropParens e3 = do
    (r1,r2) <- liftTCM2' (,) (typeCheck e1 Nothing) (typeCheck e2 Nothing)
    t1 <- typeOf r1
    t2 <- typeOf r2
    (i,c,_,_) <- ask
    case (t1,t2) of
        (Sid 0 t1 x1 y1, Sid 0 t2 x2 y2) | cmpTypes i t1 t2 -> if cmpValues i y1 x2 t1
            then return $ T.Comp `T.App` r1 `T.App` r2
            else errorTCM $ emsgLC lc "" $ etext "Terms" <+> epretty c (reify i y1 t1)
                 <+> etext "and" <+> epretty c (reify i x2 t2) <+> etext "must be equal"
        (Sid 0 t1 _ _, Sid 0 t2 _ _) -> errorTCM $ emsgLC lc "" $ etext "Types" <+> epretty c (reifyType i t1)
                                    <+> etext "and" <+> epretty c (reifyType i t2) <+> etext "must be equal"
        (Sid 0 _ _ _, t2) -> expTypeBut "Id" e2 t2
        (t1, Sid 0 _ _ _) -> expTypeBut "Id" e1 t1
        (t1, t2) -> liftTCM2' const (expTypeBut "Id" e1 t1) (expTypeBut "Id" e2 t2)
typeCheck (Arr e1 e2) Nothing = do
    (r1,r2) <- liftTCM2' (,) (isType e1) (isType e2)
    return (T.Pi [([],r1)] r2)
typeCheck (Prod e1 e2) Nothing = do
    (r1,r2) <- liftTCM2' (,) (isType e1) (isType e2)
    return (T.Sigma [([],r1)] r2)
typeCheck (Pi [] e) Nothing = typeCheck e Nothing
typeCheck (Pi (t:tv) e) Nothing = typeCheck'depType T.Pi t (Pi tv e)
typeCheck (Sigma [] e) Nothing = typeCheck e Nothing
typeCheck (Sigma (t:tv) e) Nothing = typeCheck'depType T.Sigma t (Sigma tv e)
typeCheck (Id e1 e2) Nothing = do
    r1 <- typeCheck e1 Nothing
    t <- typeOf r1
    r2 <- typeCheck e2 (Just t)
    i <- askIndex
    return $ T.Id (reifyType i t) r1 r2
typeCheck (Over t1 t) Nothing | Id e1 e2 <- dropParens t1 = do
    r <- typeCheck t Nothing
    v <- evalTCM r
    (r1,r2) <- liftTCM2' (,) (typeCheck e1 $ Just v) (typeCheck e2 $ Just v)
    return (T.Id r r1 r2)
typeCheck (Over t _) Nothing = errorTCM $ emsgLC (getPos t) "Expected term of the form _ = _" enull
typeCheck (Nat _) Nothing = return T.Nat
typeCheck (Universe (U (_,t))) Nothing = return $ T.Universe (parseLevel t)
typeCheck (App e1 e2) Nothing = do
    r1 <- typeCheck e1 Nothing
    t1 <- typeOf r1
    case t1 of
        Spi 0 _ a b -> fmap (T.App r1) $ typeCheck e2 (Just a)
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
typeCheck (Comp (PComp (lc,_))) Nothing = inferErrorMsg lc "comp"
typeCheck (Inv (PInv (lc,_))) Nothing = inferErrorMsg lc "inv"
typeCheck (InvIdp (PInvIdp (lc,_))) Nothing = inferErrorMsg lc "invIdp"

isArr :: T.DBIndex -> Value -> (Integer -> [D] -> Value -> Value) -> Maybe Value
isArr i t f =
    let r = f 0 [] (svar i t)
    in if isFreeVar 0 (i + 1) r then Nothing else Just r

evalDecl :: String -> Expr -> Maybe Expr -> TCM (M.Map String T.DBIndex, Ctx, Value, Value)
evalDecl name expr mty = do
    (er,tv) <- case mty of
        Nothing -> do
            er <- typeCheck expr Nothing
            tv <- typeOf er
            return (er,tv)
        Just ty -> do
            tr <- typeCheck ty Nothing
            tv <- evalTCM tr
            er <- typeCheck expr (Just tv)
            return (er,tv)
    ev <- evalTCM er
    (_, _, mctx, (gctx, lctx)) <- ask
    return (M.delete name mctx, (M.insert name (ev,tv) gctx, lctx), ev, tv)

eprettyType :: T.DBIndex -> [String] -> Value -> EDoc
eprettyType i c t = epretty c $ T.simplify (reifyType i t)

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
expType i c l ty = etext "Expected type:" <+> eprettyLevel c l (T.simplify $ reifyType i ty)

cmpTypesErr :: Value -> Value -> Expr -> TCM ()
cmpTypesErr t1 t2 e = do
    (i,c,_,_) <- ask
    if cmpTypes i t2 t1
        then return ()
        else errorTCM $ emsgLC (getPos e) "" $ expType i c (-1) t1 $$
            etext "But term" <+> eprettyExpr e <+> etext "has type" <+> eprettyType i c t2

expTypeBut :: String -> Expr -> Value -> TCM a
expTypeBut exp e act = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos e) "" $ etext ("Expected " ++ exp ++ " type") $$
        etext "But term" <+> eprettyExpr e <+> etext "has type" <+> eprettyHead c (T.simplify $ reifyType i act)
