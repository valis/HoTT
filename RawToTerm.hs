module RawToTerm
    ( evalRaw
    , typeOfTerm
    , rawDefsToTerm, rawExprToTerm
    ) where

import qualified Data.Map as M
import Data.List

import Syntax.Common
import Syntax.Term
import Eval
import Value
import qualified Syntax.Raw as R
import qualified Parser.AbsGrammar as E

evalRaw :: DBIndex -> M.Map String DBIndex -> Ctx -> E.Expr -> Maybe Value -> Value
evalRaw i mctx ctx e ty = eval 0 (ctxToCtxV ctx) (rawExprToTerm i mctx ctx e ty)

rawDefsToTerm :: DBIndex -> M.Map String DBIndex -> Ctx -> [E.Def] -> [Def]
rawDefsToTerm i mctx ctx [] = []
rawDefsToTerm i mctx ctx (E.DefType _ t : E.Def (E.PIdent (_,name)) args e : defs) =
    let t' = rawExprToTerm i mctx ctx t Nothing
        e' = rawExprToTerm i mctx ctx (E.Lam (error "rawDefsToTerm.Lam") (map E.Binder args) e) $
            Just $ eval 0 (ctxToCtxV ctx) t'
    in Def name (Just (t', [])) e' : rawDefsToTerm i mctx ctx defs
rawDefsToTerm i mctx ctx (E.Def (E.PIdent (_,name)) [] e : defs) =
    Def name Nothing (rawExprToTerm i mctx ctx e Nothing) : rawDefsToTerm i mctx ctx defs
rawDefsToTerm _ _ _ _ = error "rawDefsToTerm"

exprToVars :: E.Expr -> [String]
exprToVars = reverse . go
  where
    go (E.Var (E.NoArg _)) = ["_"]
    go (E.Var (E.Arg (E.PIdent (_,x)))) = [x]
    go (E.App a (E.Var (E.NoArg _))) = "_" : go a
    go (E.App a (E.Var (E.Arg (E.PIdent (_,x))))) = x : go a
    go _ = error "exprToVars"

updateCtxVar :: DBIndex -> M.Map String DBIndex -> Ctx -> [Def] -> (M.Map String DBIndex, Ctx)
updateCtxVar _ mctx ctx [] = (mctx, ctx)
updateCtxVar i mctx ctx@(gctx,lctx) (Def name Nothing expr : ds) =
    let t = typeOfTerm i ctx expr
    in updateCtxVar i (M.delete name mctx) (M.insert name (gvar name t, t) gctx, lctx) ds
updateCtxVar i mctx ctx@(gctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    let t = eval 0 (ctxToCtxV ctx) ty
    in updateCtxVar i (M.delete name mctx) (M.insert name (gvar name t, t) gctx, lctx) ds

updateCtx :: DBIndex -> Ctx -> [Def] -> Ctx
updateCtx _ ctx [] = ctx
updateCtx i actx@(ctx,lctx) (Def name Nothing expr : ds) =
    updateCtx i (M.insert name (eval 0 (ctxToCtxV actx) expr, typeOfTerm i actx expr) ctx, lctx) ds
updateCtx i actx@(ctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    updateCtx i (M.insert name (eval 0 (ctxToCtxV actx) (Lam args expr), eval 0 (ctxToCtxV actx) ty) ctx, lctx) ds

rawExprToTerm'depType :: ([([String],Term)] -> Term -> Term) -> DBIndex
    -> M.Map String DBIndex -> Ctx -> E.TypedVar -> E.Expr -> Maybe Value -> Term
rawExprToTerm'depType dt i mctx ctx@(gctx,lctx) (E.TypedVar _ vars t) e ty
    | E.Id (E.Explicit a) (E.Implicit (E.PIdent (_,b))) <- R.dropParens t =
    let vars' = exprToVars vars
        l = genericLength vars'
        a' = rawExprToTerm i mctx ctx a Nothing
        tv = typeOfTerm i ctx a'
        te = Id (reifyType i tv) (Right $ liftTermDB 1 a') (Left b)
        tev = eval 0 (ctxToCtxV ctx) te
    in dt [(vars', te)] $ rawExprToTerm (i + l + 1)
        (updateMCtx (M.insert b i mctx) (i + 1) vars') (gctx, updateLCtx tev ((svar i tv, tv) : lctx) (i + 1) l) e ty
rawExprToTerm'depType dt i mctx ctx@(gctx,lctx) (E.TypedVar _ vars t) e ty
    | E.Id (E.Implicit (E.PIdent (_,a))) (E.Explicit b) <- R.dropParens t =
    let vars' = exprToVars vars
        l = genericLength vars'
        b' = rawExprToTerm i mctx ctx b Nothing
        tv = typeOfTerm i ctx b'
        te = Id (reifyType i tv) (Left a) (Right $ liftTermDB 1 b')
        tev = eval 0 (ctxToCtxV ctx) te
    in dt [(vars', te)] $ rawExprToTerm (i + l + 1)
        (updateMCtx (M.insert a i mctx) (i + 1) vars') (gctx, updateLCtx tev ((svar i tv, tv) : lctx) (i + 1) l) e ty
rawExprToTerm'depType dt i mctx ctx@(gctx,lctx) (E.TypedVar _ vars t1) e ty
    | E.Over t2 t <- R.dropParens t1, E.Id a b <- R.dropParens t2 =
    let vars' = exprToVars vars
        l = genericLength vars'
        t' = rawExprToTerm i mctx ctx t Nothing
        tv = eval 0 (ctxToCtxV ctx) t'
    in case (a,b) of
        (E.Implicit (E.PIdent (_,x1)), E.Implicit (E.PIdent (_,x2))) ->
            let te = Id t' (Left x1) (Left x2)
                tev = eval 0 (ctxToCtxV ctx) te
            in dt [(vars', te)] $ rawExprToTerm (i + l + 2)
                (updateMCtx (M.insert x2 (i + 1) $ M.insert x1 i mctx) (i + 2) vars')
                (gctx, updateLCtx tev ((svar (i + 1) tv, tv) : (svar i tv, tv) : lctx) (i + 2) l) e ty
        (E.Implicit (E.PIdent (_,x1)), E.Explicit e2) ->
            let te = Id t' (Left x1) (Right $ rawExprToTerm i mctx ctx e2 $ Just tv)
                tev = eval 0 (ctxToCtxV ctx) te
            in dt [(vars', te)] $ rawExprToTerm (i + l + 1) (updateMCtx (M.insert x1 i mctx) (i + 1) vars')
                (gctx, updateLCtx tev ((svar i tv, tv) : lctx) (i + 1) l) e ty
        (E.Explicit e1, E.Implicit (E.PIdent (_,x2))) ->
            let te = Id t' (Right $ rawExprToTerm i mctx ctx e1 $ Just tv) (Left x2)
                tev = eval 0 (ctxToCtxV ctx) te
            in dt [(vars', te)] $ rawExprToTerm (i + l + 1) (updateMCtx (M.insert x2 i mctx) (i + 1) vars')
                (gctx, updateLCtx tev ((svar i tv, tv) : lctx) (i + 1) l) e ty
        (E.Explicit e1, E.Explicit e2) ->
            let te = Id t' (Right $ rawExprToTerm i mctx ctx e1 $ Just tv) (Right $ rawExprToTerm i mctx ctx e2 $ Just tv)
                tev = eval 0 (ctxToCtxV ctx) te
            in dt [(vars', te)] $ rawExprToTerm (i + l) (updateMCtx mctx i vars') (gctx, updateLCtx tev lctx i l) e ty
rawExprToTerm'depType dt i mctx ctx@(gctx,lctx) (E.TypedVar _ vars t) e ty =
    let vars' = exprToVars vars
        l = genericLength vars'
        t' = rawExprToTerm i mctx ctx t ty
        tv = eval 0 (ctxToCtxV ctx) t'
    in dt [(vars',t')] $ rawExprToTerm (i + l) (updateMCtx mctx i vars') (gctx, updateLCtx tv lctx i l) e ty

updateMCtx :: M.Map String DBIndex -> DBIndex -> [String] -> M.Map String DBIndex
updateMCtx mctx i [] = mctx
updateMCtx mctx i (v:vs) = updateMCtx (M.insert v i mctx) (i + 1) vs

updateLCtx :: Value -> [(Value,Value)] -> DBIndex -> DBIndex -> [(Value,Value)]
updateLCtx _ lctx _ 0 = lctx
updateLCtx tv lctx i n = updateLCtx tv ((svar i tv, tv) : lctx) (i + 1) (n - 1)

rawExprToTerm :: DBIndex -> M.Map String DBIndex -> Ctx -> E.Expr -> Maybe Value -> Term
rawExprToTerm i mctx ctx e (Just (Ne _ t)) | NoVar <- t 0 = rawExprToTerm i mctx ctx e Nothing
rawExprToTerm i mctx ctx (E.Let defs expr) ty =
    let defs' = rawDefsToTerm i mctx ctx defs
        (mctx',ctx') = updateCtxVar i mctx ctx defs'
    in Let defs' (rawExprToTerm i mctx' ctx' expr ty)
rawExprToTerm i mctx ctx (E.Lam _ [] expr) ty = rawExprToTerm i mctx ctx expr ty
rawExprToTerm i mctx (ctx,lctx) (E.Lam j (arg:args) expr) (Just (Spi 0 _ t s)) =
    let v = R.unBinder arg
        vv = svar i t
    in Lam [v] $ rawExprToTerm (i + 1) (M.insert v i mctx) (ctx, (vv,t):lctx) (E.Lam j args expr) $ Just (s 0 [] vv)
rawExprToTerm i _ _ (E.Lam _ _ _) _ = error "rawExprToTerm.Lam"
rawExprToTerm i _ _ (E.Pi [] e) ty = error "rawExprToTerm.Pi"
rawExprToTerm i mctx ctx (E.Pi [t] e) ty = rawExprToTerm'depType Pi i mctx ctx t e ty
rawExprToTerm i mctx ctx (E.Pi (t:ts) e) ty = rawExprToTerm i mctx ctx (E.Pi [t] $ E.Pi ts e) ty
rawExprToTerm i _ _ (E.Sigma [] e) ty = error "rawExprToTerm.Sigma"
rawExprToTerm i mctx ctx (E.Sigma [t] e) ty = rawExprToTerm'depType Sigma i mctx ctx t e ty
rawExprToTerm i mctx ctx (E.Sigma (t:ts) e) ty = rawExprToTerm i mctx ctx (E.Sigma [t] $ E.Sigma ts e) ty
rawExprToTerm i mctx ctx (E.Arr e1 e2) ty = Pi [([], rawExprToTerm i mctx ctx e1 ty)] (rawExprToTerm i mctx ctx e2 ty)
rawExprToTerm i mctx ctx (E.Prod e1 e2) ty = Sigma [([], rawExprToTerm i mctx ctx e1 ty)] (rawExprToTerm i mctx ctx e2 ty)
rawExprToTerm i mctx ctx (E.Pair e1 e2) (Just (Ssigma 0 _ a b)) =
    Pair (rawExprToTerm i mctx ctx e1 $ Just a)
         (rawExprToTerm i mctx ctx e2 $ Just $ b 0 [] $ evalRaw i mctx ctx e1 $ Just a)
rawExprToTerm i _ _ (E.Pair e1 e2) (Just _) = error "rawExprToTerm.Pair"
rawExprToTerm i _ _ (E.Proj1 _) _ = Proj1
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Proj1 _ <- R.dropParens e1 = App Proj1 (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i _ _ (E.Proj2 _) _ = Proj2
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Proj2 _ <- R.dropParens e1 = App Proj2 (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.Pair e1 e2) Nothing =
    Pair (rawExprToTerm i mctx ctx e1 Nothing) (rawExprToTerm i mctx ctx e2 Nothing)
rawExprToTerm i mctx ctx (E.Id (E.Explicit e1) (E.Implicit (E.PIdent (_,x2)))) _ =
    let e1' = rawExprToTerm i mctx ctx e1 Nothing
        t1 = typeOfTerm i ctx e1'
    in Id (reifyType i t1) (Right $ liftTermDB 1 e1') (Left x2)
rawExprToTerm i mctx ctx (E.Id (E.Implicit (E.PIdent (_,x1))) (E.Explicit e2)) _ =
    let e2' = rawExprToTerm i mctx ctx e2 Nothing
        t2 = typeOfTerm i ctx e2'
    in Id (reifyType i t2) (Left x1) (Right $ liftTermDB 1 e2')
rawExprToTerm i mctx ctx (E.Id (E.Explicit e1) (E.Explicit e2)) _ =
    let e1' = rawExprToTerm i mctx ctx e1 Nothing
        t1 = typeOfTerm i ctx e1'
    in Id (reifyType i t1) (Right e1') $ Right $ rawExprToTerm i mctx ctx e2 (Just t1)
rawExprToTerm i mctx ctx (E.Id _ _) _ = error "rawExprToTerm.Id"
rawExprToTerm i mctx ctx@(gctx,lctx) (E.Over e1 t) _ | E.Id a b <- R.dropParens e1 =
    let t' = rawExprToTerm i mctx ctx t Nothing
        tv = typeOfTerm i ctx t'
    in case (a,b) of
        (E.Implicit (E.PIdent (_,x1)), E.Implicit (E.PIdent (_,x2))) -> Id t' (Left x1) (Left x2)
        (E.Implicit (E.PIdent (_,x1)), E.Explicit e2) ->
            Id t' (Left x1) (Right $ rawExprToTerm (i + 1) (M.insert x1 i mctx) (gctx, (svar i tv, tv):lctx) e2 $ Just tv)
        (E.Explicit e1, E.Implicit (E.PIdent (_,x2))) ->
            Id t' (Right $ rawExprToTerm (i + 1) (M.insert x2 i mctx) (gctx, (svar i tv, tv):lctx) e1 $ Just tv) (Left x2)
        (E.Explicit e1, E.Explicit e2) -> Id t' (Right $ rawExprToTerm i mctx ctx e1 $ Just tv)
                                                (Right $ rawExprToTerm i mctx ctx e2 $ Just tv)
rawExprToTerm i mctx ctx (E.Over _ _) _ = error "rawExprToTerm.Over"
rawExprToTerm i mctx ctx (E.Pmap _) _ = Pmap
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Pmap _ <- R.dropParens e1 = App Pmap (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1' e2) _
    | E.App e3 e4 <- R.dropParens e1'
    , E.Pmap _ <- R.dropParens e3
    , E.App e5 e1 <- R.dropParens e4
    , E.Idp _ <- R.dropParens e5 =
        let e2' = rawExprToTerm i mctx ctx e2 Nothing
        in case typeOfTerm i ctx e2' of
            Sid 0 t _ _ -> let e' = rawExprToTerm i mctx ctx e1 $ Just $ sarr 0 t $ Ne [] (const NoVar)
                         in App (App Pmap (App Idp e')) e2'
            _ -> error "rawExprToTerm.App.App.Idp"
rawExprToTerm i mctx ctx (E.App e1' e2) _ | E.App e3 e1 <- R.dropParens e1', E.Pmap _ <- R.dropParens e3 =
    App (App Pmap (rawExprToTerm i mctx ctx e1 Nothing)) (rawExprToTerm i mctx ctx e2 Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid 0 t _ _)) | E.Idp _ <- R.dropParens e1 =
    App Idp $ rawExprToTerm i mctx ctx e (Just t)
rawExprToTerm i _ _ (E.App e1 e) (Just _) | E.Idp _ <- R.dropParens e1 = error "rawExprToTerm.App.Idp"
rawExprToTerm i mctx ctx (E.App e1 e) Nothing | E.Idp _ <- R.dropParens e1 = App Idp (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Coe _ <- R.dropParens e1 = App Coe (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid 0 t@(Spi 0 x a b) f g)) | E.Ext _ <- R.dropParens e1 =
    App (Ext (reify i f t) (reify i g t)) $ rawExprToTerm i mctx ctx e $ Just $
    Spi 0 x a $ \k m v ->
        let r1 = b k m v
            r2 = app k (action m f) v 
            r3 = app k (action m g) v
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)], []) $ Id (Var "r1") (Right $ Var "r2") (Right $ Var "r3")
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid 0 t@(Ssigma 0 x a b) p q)) | E.Ext _ <- R.dropParens e1 =
    App (ExtSigma (reify i p t) (reify i q t)) $ rawExprToTerm i mctx ctx e $ Just $
    Ssigma 0 x (Sid 0 a (proj1 p) (proj1 q)) $ \k m v ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x b) v (action m $ proj2 p)
            r3 = proj2 q
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)], []) $ Id (Var "r1") (Right $ Var "r2") (Right $ Var "r3")
rawExprToTerm i _ _ (E.Ext _) (Just (Spi 0 _ a b)) = case b 0 [] (error "rawExprToTerm.Ext.Var") of
    Sid 0 t@(Spi 0 _ _ _) f g -> Ext (reify i f t) (reify i g t)
    Sid 0 t@(Ssigma 0 _ _ _) p q -> ExtSigma (reify i p t) (reify i q t)
    _ -> error "rawExprToTerm.Ext.Pi"
rawExprToTerm i _ _ (E.Ext _) _ = error "rawExprToTerm.Ext"
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid 0 t x y)) | E.Inv _ <- R.dropParens e1 =
    App Inv $ rawExprToTerm i mctx ctx e $ Just (Sid 0 t y x)
rawExprToTerm i _ _ (E.App e1 e) (Just _) | E.Inv _ <- R.dropParens e1 = error "rawExprToTerm.App.Inv"
rawExprToTerm i mctx ctx (E.App e1 e) Nothing | E.Inv _ <- R.dropParens e1 = App Inv (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.InvIdp _ <- R.dropParens e1 = App InvIdp (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1' e2) _ | E.App e3 e1 <- R.dropParens e1', E.Comp _ <- R.dropParens e3 =
    Comp `App` rawExprToTerm i mctx ctx e1 Nothing `App` rawExprToTerm i mctx ctx e2 Nothing
rawExprToTerm i mctx ctx (E.App e1 e2) _ =
    let e1' = rawExprToTerm i mctx ctx e1 Nothing
    in case typeOfTerm i ctx e1' of
        Spi 0 _ t2 _ -> App e1' $ rawExprToTerm i mctx ctx e2 (Just t2)
        Sid 0 _ _ _ -> App e1' (rawExprToTerm i mctx ctx e2 Nothing)
        _ -> error $ "rawExprToTerm.App"
rawExprToTerm _ _ _ (E.Var (E.NoArg _)) _ = NoVar
rawExprToTerm _ _ _ (E.Var (E.Arg (E.PIdent (_,"_")))) _ = NoVar
rawExprToTerm i mctx _ (E.Var (E.Arg (E.PIdent (_,v)))) _ = maybe (Var v) (\l -> LVar $ i - l - 1) (M.lookup v mctx)
rawExprToTerm _ _ _ (E.Nat _) _ = Nat
rawExprToTerm _ _ _ (E.Suc _) _ = Suc
rawExprToTerm _ _ _ (E.Rec _) _ = Rec
rawExprToTerm _ _ _ (E.Idp _) _ = Idp
rawExprToTerm _ _ _ (E.Coe _) _ = Coe
rawExprToTerm _ _ _ (E.Iso _) _ = Iso
rawExprToTerm _ _ _ (E.Comp _) _ = Comp
rawExprToTerm _ _ _ (E.Inv _) _ = Inv
rawExprToTerm _ _ _ (E.InvIdp _) _ = InvIdp
rawExprToTerm _ _ _ (E.NatConst (E.PInt (_,x))) _ = NatConst (read x)
rawExprToTerm _ _ _ (E.Universe (E.U (_,x))) _ = Universe (parseLevel x)
rawExprToTerm i mctx ctx (E.Paren _ e) ty = rawExprToTerm i mctx ctx e ty
rawExprToTerm i mctx ctx (E.Typed e1 e2) _ =
    let e2' = rawExprToTerm i mctx ctx e2 $ Just (Stype maxBound)
    in Typed (rawExprToTerm i mctx ctx e1 $ Just $ eval 0 (ctxToCtxV ctx) e2') e2'

typeOfTerm :: DBIndex -> Ctx -> Term -> Value
typeOfTerm i ctx (Let defs e) = typeOfTerm i (updateCtx i ctx defs) e
typeOfTerm i ctx (Lam [] e) = typeOfTerm i ctx e
typeOfTerm _ _ (Lam _ _) = error "typeOfTerm.Lam"
typeOfTerm i ctx (Pi [] e) = typeOfTerm i ctx e
typeOfTerm i (ctx,lctx) (Pi ((vars,t):vs) e) =
    let r = typeOfTerm (i + genericLength vars)
            (ctx, updateLCtx (eval 0 (ctxToCtxV (ctx,lctx)) t) lctx i $ genericLength vars) (Pi vs e)
    in case (typeOfTerm i (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Pi"
typeOfTerm i ctx (Sigma [] e) = typeOfTerm i ctx e
typeOfTerm i (ctx,lctx) (Sigma ((vars,t):vs) e) =
    let r = typeOfTerm (i + genericLength vars)
            (ctx, updateLCtx (eval 0 (ctxToCtxV (ctx,lctx)) t) lctx i $ genericLength vars) (Sigma vs e)
    in case (typeOfTerm i (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Sigma"
typeOfTerm i ctx (Pair e1 e2) = sprod 0 (typeOfTerm i ctx e1) (typeOfTerm i ctx e2)
typeOfTerm i ctx Proj1 = error "typeOfTerm.Proj1"
typeOfTerm i ctx (App Proj1 e) = case typeOfTerm i ctx e of
    Ssigma 0 _ a _ -> a
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm i ctx Proj2 = error "typeOfTerm.Proj2"
typeOfTerm i ctx (App Proj2 e) = case typeOfTerm i ctx e of
    Ssigma 0 _ _ b -> b 0 [] $ eval 0 (ctxToCtxV ctx) (App Proj1 e)
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm i ctx (Id t _ _) = typeOfTerm i ctx t
typeOfTerm i ctx (App Idp e) =
    let v = eval 0 (ctxToCtxV ctx) e
    in Sid 0 (typeOfTerm i ctx e) v v
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfTerm i ctx (App (App Pmap (App Idp e1)) e2) =
    let e' = eval 0 (ctxToCtxV ctx) e1
    in case typeOfTerm i ctx e2 of
        Sid 0 t a b -> typeOfLam i ctx e1 t (app 0 e' a) (app 0 e' b) (eval 0 (ctxToCtxV ctx) e2)
        _ -> error "typeOfTerm.App.App.Pmap.Idp"
typeOfTerm i ctx (App (App Pmap e1) e2) =
    case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
        (Sid 0 (Spi 0 v _ b) f g, Sid 0 _ x y) ->
            Sid 0 (b 0 [] y) (trans 0 (Slam v b) (eval 0 (ctxToCtxV ctx) e2) (app 0 f x)) (app 0 g y)
        _ -> error "typeOfTerm.App.App.Pmap"
typeOfTerm i ctx (App Coe e) = case typeOfTerm i ctx e of
    Sid 0 _ x y -> sarr 0 x y
    _ -> error "typeOfTerm.App.Coe"
typeOfTerm i ctx (App Inv e) = case typeOfTerm i ctx e of
    Sid 0 t x y -> Sid 0 t y x
    _ -> error "typeOfTerm.App.Inv"
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeOfTerm i ctx (App InvIdp e) = case typeOfTerm i ctx e of
    t@(Sid 0 _ _ _) ->
        let e' = eval 0 (ctxToCtxV ctx) e
        in Sid 0 (Sid 0 t e' e') (comp 0 (inv 0 e') e') (idp 0 e')
    _ -> error "typeOfTerm.App.InvIdp"
typeOfTerm i ctx (App (App Comp e1) e2) = case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
    (Sid 0 t x _, Sid 0 _ _ z) -> Sid 0 t x z
    _ -> error "typeOfTerm.App.Comp"
typeOfTerm i ctx (App e1 e2) = case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
    (Spi 0 _ _ b, _) -> b 0 [] $ eval 0 (ctxToCtxV ctx) e2
    (Sid 0 (Spi 0 _ _ t) f g, Sid 0 _ a b) -> Sid 0 (t 0 [] $ error "typeOfTerm.App.Id") (app 0 f a) (app 0 g b)
    _ -> error "typeOfTerm.App"
typeOfTerm _ (_,ctx) (LVar v) = snd $ ctx `genericIndex` v
typeOfTerm i ctx NoVar = error "typeOfTerm.NoVar"
typeOfTerm i (ctx,_) (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v
    Just (_,t) -> t
typeOfTerm i _ Nat = Stype (Finite 0)
typeOfTerm i _ Suc = sarr 0 Snat Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm i _ Rec = eval 0 (M.empty,[]) $ Pi [(["P"], Pi [([],Nat)] $ Universe Omega)] $
    Pi [([], App (LVar 0) $ NatConst 0)] $ Pi [([], iht)] $ Pi [(["x"],Nat)] $ App (LVar 1) (LVar 0)
  where iht = Pi [(["x"],Nat)] $ Pi [([], App (LVar 1) (LVar 0))] $ App (LVar 1) $ App Suc (LVar 0)
typeOfTerm i ctx (Typed _ t) = eval 0 (ctxToCtxV ctx) t
typeOfTerm i ctx (Ext f g) = Sid 0 (typeOfTerm i ctx f) (eval 0 (ctxToCtxV ctx) f) (eval 0 (ctxToCtxV ctx) g)
typeOfTerm i ctx (ExtSigma p q) = Sid 0 (typeOfTerm i ctx p) (eval 0 (ctxToCtxV ctx) p) (eval 0 (ctxToCtxV ctx) q)
typeOfTerm _ _ (NatConst _) = Snat
typeOfTerm _ _ (Universe l) = Stype (succ l)
typeOfTerm _ _ Pmap = error "typeOfTerm.Pmap"
typeOfTerm _ _ Idp = error "typeOfTerm.Idp"
typeOfTerm _ _ Coe = error "typeOfTerm.Coe"
typeOfTerm _ _ Comp = error "typeOfTerm.Comp"
typeOfTerm _ _ Inv = error "typeOfTerm.Inv"
typeOfTerm _ _ InvIdp = error "typeOfTerm.InvIdp"
typeOfTerm _ _ Iso = 
    let term = Pi [(["A"],Universe $ pred $ pred maxBound)] $
               Pi [(["B"],Universe $ pred $ pred maxBound)] $
               Pi [(["f"],Pi [([],LVar 1)] $ LVar 0)] $
               Pi [(["g"],Pi [([],LVar 1)] $ LVar 2)] $
               Pi [([],Pi [(["a"],LVar 3)] $ Id (LVar 4) (Right $ LVar 1 `App` (LVar 2 `App` LVar 0)) (Right $ LVar 0))] $
               Pi [([],Pi [(["b"],LVar 2)] $ Id (LVar 3) (Right $ LVar 2 `App` (LVar 1 `App` LVar 0)) (Right $ LVar 0))] $
               Id (Universe $ pred $ pred maxBound) (Right $ Var "A") (Right $ Var "B")
    in eval 0 (M.empty,[]) term

typeOfLam :: DBIndex -> Ctx -> Term -> Value -> Value -> Value -> Value -> Value
typeOfLam i ctx (Let defs e) t a b p = typeOfLam i (updateCtx i ctx defs) e t a b p
typeOfLam i ctx (Lam [] e) t a b p = typeOfLam i ctx e t a b p
typeOfLam i (ctx,lctx) (Lam (x:xs) e) t a b _ = Sid 0 (typeOfTerm i (ctx, (error "typeOfLam.Var", t) : lctx) (Lam xs e)) a b
typeOfLam i ctx e t a b p = case typeOfTerm i ctx e of
    Spi 0 v _ r -> Sid 0 (r 0 [] b) (trans 0 (Slam v r) p a) b
    _ -> error "typeOfLam.Pi"
