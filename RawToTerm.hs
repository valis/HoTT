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

evalRaw :: M.Map String DBIndex -> Ctx -> E.Expr -> Maybe Value -> Value
evalRaw mctx ctx e ty = eval 0 (ctxToCtxV ctx) (rawExprToTerm mctx ctx e ty)

rawDefsToTerm :: M.Map String DBIndex -> Ctx -> [E.Def] -> [Def]
rawDefsToTerm mctx ctx [] = []
rawDefsToTerm mctx ctx (E.DefType _ t : E.Def (E.PIdent (_,name)) args e : defs) =
    let t' = rawExprToTerm mctx ctx t Nothing
        e' = rawExprToTerm mctx ctx (E.Lam (error "rawDefsToTerm.Lam") (map E.Binder args) e) $
            Just $ eval 0 (ctxToCtxV ctx) t'
    in Def name (Just (t', [])) e' : rawDefsToTerm mctx ctx defs
rawDefsToTerm mctx ctx (E.Def (E.PIdent (_,name)) [] e : defs) =
    Def name Nothing (rawExprToTerm mctx ctx e Nothing) : rawDefsToTerm mctx ctx defs
rawDefsToTerm _ _ _ = error "rawDefsToTerm"

exprToVars :: E.Expr -> [String]
exprToVars = reverse . go
  where
    go (E.Var (E.NoArg _)) = ["_"]
    go (E.Var (E.Arg (E.PIdent (_,x)))) = [x]
    go (E.App a (E.Var (E.NoArg _))) = "_" : go a
    go (E.App a (E.Var (E.Arg (E.PIdent (_,x))))) = x : go a
    go _ = error "exprToVars"

updateCtxVar :: DBIndex -> Ctx -> [Def] -> Ctx
updateCtxVar _ ctx [] = ctx
updateCtxVar i ctx (Def name Nothing expr : ds) =
    let t = typeOfTerm i ctx expr
    in updateCtxVar i (M.insert name (svar name t, t) ctx) ds
updateCtxVar i ctx (Def name (Just (ty,args)) expr : ds) =
    let t = eval 0 (ctxToCtxV ctx) ty
    in updateCtxVar i (M.insert name (svar name t, t) ctx) ds

updateCtx :: Ctx -> [Def] -> Ctx
updateCtx _ ctx [] = ctx
updateCtx i (ctx,lctx) (Def name Nothing expr : ds) =
    updateCtx i (M.insert name (eval 0 (ctxToCtxV ctx) expr, typeOfTerm i ctx expr) ctx, lctx) ds
updateCtx i (ctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    updateCtx i (M.insert name (eval 0 (ctxToCtxV ctx) (Lam args expr), eval 0 (ctxToCtxV ctx) ty) ctx, lctx) ds

rawExprToTerm'depType :: ([([String],Term)] -> Term -> Term) -> M.Map String DBIndex
    -> Ctx -> E.TypedVar -> E.Expr -> Maybe Value -> Term
rawExprToTerm'depType dt lctx ctx (E.TypedVar _ vars t) e ty = 
    dt [(exprToVars vars, rawExprToTerm lctx ctx t ty)] $ rawExprToTerm lctx (updateCtx ctx (exprToVars vars)) e ty
  where
    tv = evalRaw lctx ctx t ty
    updateCtx ctx [] = ctx
    updateCtx ctx (v:vs) = updateCtx (M.insert v (svar v tv, tv) ctx) vs

dropParens :: E.Expr -> E.Expr
dropParens (E.Paren _ e) = dropParens e
dropParens e = e

rawExprToTerm :: DBIndex -> M.Map String DBIndex -> Ctx -> E.Expr -> Maybe Value -> Term
rawExprToTerm lctx ctx e (Just (Ne _ (Var "_"))) = rawExprToTerm lctx ctx e Nothing
rawExprToTerm lctx ctx (E.Let defs expr) ty =
    let defs' = rawDefsToTerm lctx ctx defs
    in Let defs' $ rawExprToTerm lctx (updateCtxVar ctx defs') expr ty
rawExprToTerm lctx ctx (E.Lam _ [] expr) ty = rawExprToTerm lctx ctx expr ty
rawExprToTerm lctx ctx (E.Lam i (arg:args) expr) (Just (Spi _ fv t s)) =
    let (v,expr') = R.renameExpr fv (R.unBinder arg) (E.Lam i args expr)
        vv = svar v t
    in Lam [v] $ rawExprToTerm lctx (M.insert v (vv, t) ctx) expr' $ Just (s 0 [] vv)
rawExprToTerm _ _ (E.Lam _ _ _) _ = error "rawExprToTerm.Lam"
rawExprToTerm _ _ (E.Pi [] e) ty = error "rawExprToTerm.Pi"
rawExprToTerm lctx ctx (E.Pi [t] e) ty = rawExprToTerm'depType Pi lctx ctx t e ty
rawExprToTerm lctx ctx (E.Pi (t:ts) e) ty = rawExprToTerm lctx ctx (E.Pi [t] $ E.Pi ts e) ty
rawExprToTerm _ _ (E.Sigma [] e) ty = error "rawExprToTerm.Sigma"
rawExprToTerm lctx ctx (E.Sigma [t] e) ty = rawExprToTerm'depType Sigma lctx ctx t e ty
rawExprToTerm lctx ctx (E.Sigma (t:ts) e) ty = rawExprToTerm lctx ctx (E.Sigma [t] $ E.Sigma ts e) ty
rawExprToTerm lctx ctx (E.Arr e1 e2) ty = Pi [([], rawExprToTerm lctx ctx e1 ty)] (rawExprToTerm lctx ctx e2 ty)
rawExprToTerm lctx ctx (E.Prod e1 e2) ty = Sigma [([], rawExprToTerm lctx ctx e1 ty)] (rawExprToTerm lctx ctx e2 ty)
rawExprToTerm lctx ctx (E.Pair e1 e2) (Just (Ssigma _ _ a b)) =
    Pair (rawExprToTerm lctx ctx e1 $ Just a) (rawExprToTerm lctx ctx e2 $ Just $ b 0 [] $ evalRaw lctx ctx e1 $ Just a)
rawExprToTerm _ _ (E.Pair e1 e2) (Just _) = error "rawExprToTerm.Pair"
rawExprToTerm _ _ (E.Proj1 _) _ = Proj1
rawExprToTerm lctx ctx (E.App e1 e) _ | E.Proj1 _ <- dropParens e1 = App Proj1 (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm _ _ (E.Proj2 _) _ = Proj2
rawExprToTerm lctx ctx (E.App e1 e) _ | E.Proj2 _ <- dropParens e1 = App Proj2 (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm lctx ctx (E.Pair e1 e2) Nothing = Pair (rawExprToTerm lctx ctx e1 Nothing) (rawExprToTerm lctx ctx e2 Nothing)
rawExprToTerm lctx ctx (E.Id e1 e2) _ =
    let e1' = rawExprToTerm lctx ctx e1 Nothing
        t1 = typeOfTerm i ctx e1'
    in Id (reifyType t1) e1' $ rawExprToTerm lctx ctx e2 (Just t1)
rawExprToTerm lctx ctx (E.Pmap _) _ = Pmap
rawExprToTerm lctx ctx (E.App e1 e) _ | E.Pmap _ <- dropParens e1 = App Pmap (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm lctx ctx (E.App e1' e2) _
    | E.App e3 e4 <- dropParens e1'
    , E.Pmap _ <- dropParens e3
    , E.App e5 e1 <- dropParens e4
    , E.Idp _ <- dropParens e5 =
        let e2' = rawExprToTerm lctx ctx e2 Nothing
        in case typeOfTerm i ctx e2' of
            Sid t _ _ -> let e' = rawExprToTerm lctx ctx e1 $ Just $ t `sarr` svar "_" (Stype maxBound)
                         in App (App Pmap (App Idp e')) e2'
            _ -> error "rawExprToTerm.App.App.Idp"
rawExprToTerm lctx ctx (E.App e1' e2) _ | E.App e3 e1 <- dropParens e1', E.Pmap _ <- dropParens e3 =
    App (App Pmap (rawExprToTerm lctx ctx e1 Nothing)) (rawExprToTerm lctx ctx e2 Nothing)
rawExprToTerm lctx ctx (E.App e1 e) (Just (Sid t _ _)) | E.Idp _ <- dropParens e1 =
    App Idp $ rawExprToTerm lctx ctx e (Just t)
rawExprToTerm _ _ (E.App e1 e) (Just _) | E.Idp _ <- dropParens e1 = error "rawExrToTerm.App.Idp"
rawExprToTerm lctx ctx (E.App e1 e) Nothing | E.Idp _ <- dropParens e1 = App Idp (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm lctx ctx (E.App e1 e) _ | E.Coe _ <- dropParens e1 = App Coe (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm lctx ctx (E.App e1 e) (Just (Sid t@(Spi x fv a b) f g)) | E.Ext _ <- dropParens e1 =
    App (Ext (reify f t) (reify g t)) $ rawExprToTerm lctx ctx e $ Just $
    Spi x a $ \k m v ->
        let r1 = b k m v
            r2 = app k (action m f) v 
            r3 = app k (action m g) v
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)]) $ Id (Var "r1") (Var "r2") (Var "r3")
rawExprToTerm lctx ctx (E.App e1 e) (Just (Sid t@(Ssigma x fv a b) p q)) | E.Ext _ <- dropParens e1 =
    App (ExtSigma (reify p t) (reify q t)) $ rawExprToTerm lctx ctx e $ Just $
    Ssigma x (Sid a (proj1 p) (proj1 q)) $ \k m v ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x fv b) v (action m $ proj2 p)
            r3 = proj2 q
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)]) $ Id (Var "r1") (Var "r2") (Var "r3")
rawExprToTerm _ _ (E.Ext _) (Just (Spi _ _ a b)) = case b 0 [] (error "rawExprToTerm.Ext.Var") of
    Sid t@(Spi _ _ _ _) f g -> Ext (reify f t) (reify g t)
    Sid t@(Ssigma _ _ _ _) p q -> ExtSigma (reify p t) (reify q t)
    _ -> error "rawExprToTerm.Ext.Pi"
rawExprToTerm _ _ (E.Ext _) _ = error "rawExprToTerm.Ext"
rawExprToTerm lctx ctx (E.App e1 e) (Just (Sid t x y)) | E.Inv _ <- dropParens e1 =
    App Inv $ rawExprToTerm lctx ctx e $ Just (Sid t y x)
rawExprToTerm _ _ (E.App e1 e) (Just _) | E.Inv _ <- dropParens e1 = error "rawExprToTerm.App.Inv"
rawExprToTerm lctx ctx (E.App e1 e) Nothing | E.Inv _ <- dropParens e1 = App Inv (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm lctx ctx (E.App e1 e) _ | E.InvIdp _ <- dropParens e1 = App InvIdp (rawExprToTerm lctx ctx e Nothing)
rawExprToTerm lctx ctx (E.App e1' e2) _ | E.App e3 e1 <- dropParens e1', E.Comp _ <- dropParens e3 =
    Comp `App` rawExprToTerm lctx ctx e1 Nothing `App` rawExprToTerm lctx ctx e2 Nothing
rawExprToTerm lctx ctx (E.App e1 e2) _ =
    let e1' = rawExprToTerm lctx ctx e1 Nothing
    in case typeOfTerm i ctx e1' of
        Spi _ _ t2 _ -> App e1' $ rawExprToTerm lctx ctx e2 (Just t2)
        Sid _ _ _ -> App e1' (rawExprToTerm lctx ctx e2 Nothing)
        _ -> error "rawExprToTerm.App"
rawExprToTerm _ _ (E.Var (E.NoArg _)) _ = NoVar
rawExprToTerm _ _ (E.Var (E.Arg (E.PIdent (_,"_")))) _ = NoVar
rawExprToTerm lctx _ (E.Var (E.Arg (E.PIdent (_,v)))) _ = maybe (Var v) LVar (M.lookup v lctx)
rawExprToTerm _ _ (E.Nat _) _ = Nat
rawExprToTerm _ _ (E.Suc _) _ = Suc
rawExprToTerm _ _ (E.Rec _) _ = Rec
rawExprToTerm _ _ (E.Idp _) _ = Idp
rawExprToTerm _ _ (E.Coe _) _ = Coe
rawExprToTerm _ _ (E.Iso _) _ = Iso
rawExprToTerm _ _ (E.Comp _) _ = Comp
rawExprToTerm _ _ (E.Inv _) _ = Inv
rawExprToTerm _ _ (E.InvIdp _) _ = InvIdp
rawExprToTerm _ _ (E.NatConst (E.PInt (_,x))) _ = NatConst (read x)
rawExprToTerm _ _ (E.Universe (E.U (_,x))) _ = Universe (parseLevel x)
rawExprToTerm lctx ctx (E.Paren _ e) ty = rawExprToTerm lctx ctx e ty
rawExprToTerm lctx ctx (E.Typed e1 e2) _ =
    let e2' = rawExprToTerm lctx ctx e2 $ Just (Stype maxBound)
    in Typed (rawExprToTerm lctx ctx e1 $ Just $ eval 0 (ctxToCtxV ctx) e2') e2'

updateLCtx :: DBIndex -> Value -> [(Value,Value)] -> [String] -> [(Value,Value)]
updateLCtx _ tv lctx [] = lctx
updateLCtx i tv lctx (_:vs) = updateLCtx (i + 1) tv ((svar i tv, tv) : lctx) vs

typeOfTerm :: DBIndex -> Ctx -> Term -> Value
typeOfTerm i ctx (Let defs e) = typeOfTerm i (updateCtx ctx defs) e
typeOfTerm i ctx (Lam [] e) = typeOfTerm i ctx e
typeOfTerm _ _ (Lam _ _) = error "typeOfTerm.Lam"
typeOfTerm i ctx (Pi [] e) = typeOfTerm i ctx e
typeOfTerm i (ctx,lctx) (Pi ((vars,t):vs) e) =
    let r = typeOfTerm (i + length vars) (ctx, updateLCtx i (eval 0 (ctxToCtxV (ctx,lctx)) t) lctx vars) (Pi vs e)
    in case (typeOfTerm i (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Pi"
typeOfTerm i ctx (Sigma [] e) = typeOfTerm i ctx e
typeOfTerm i (ctx,lctx) (Sigma ((vars,t):vs) e) =
    let r = typeOfTerm (i + length vars) (ctx, updateLCtx i (eval 0 (ctxToCtxV (ctx,lctx)) t) lctx vars) (Sigma vs e)
    in case (typeOfTerm i (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Sigma"
typeOfTerm i ctx (Pair e1 e2) = typeOfTerm i ctx e1 `sprod` typeOfTerm i ctx e2
typeOfTerm i ctx Proj1 = error "typeOfTerm.Proj1"
typeOfTerm i ctx (App Proj1 e) = case typeOfTerm i ctx e of
    Ssigma _ a _ -> a
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm i ctx Proj2 = error "typeOfTerm.Proj2"
typeOfTerm i ctx (App Proj2 e) = case typeOfTerm i ctx e of
    Ssigma _ _ b -> b 0 [] $ eval 0 (ctxToCtxV ctx) (App Proj1 e)
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm i ctx (Id t _ _) = typeOfTerm i ctx t
typeOfTerm i ctx (App Idp e) =
    let v = eval 0 (ctxToCtxV ctx) e
    in Sid (typeOfTerm i ctx e) v v
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfTerm i ctx (App (App Pmap (App Idp e1)) e2) =
    let e' = eval 0 (ctxToCtxV ctx) e1
    in case typeOfTerm i ctx e2 of
        Sid t a b -> typeOfLam i ctx e1 t (app 0 e' a) (app 0 e' b) (eval 0 (ctxToCtxV ctx) e2)
        _ -> error "typeOfTerm.App.App.Pmap.Idp"
typeOfTerm i ctx (App (App Pmap e1) e2) =
    case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
        (Sid (Spi v fv _ b) f g, Sid _ x y) ->
            Sid (b 0 [] y) (trans 0 (Slam v fv b) (eval 0 (ctxToCtxV ctx) e2) (app 0 f x)) (app 0 g y)
        _ -> error "typeOfTerm.App.App.Pmap"
typeOfTerm i ctx (App Coe e) = case typeOfTerm i ctx e of
    Sid _ x y -> x `sarr` y
    _ -> error "typeOfTerm.App.Coe"
typeOfTerm i ctx (App Inv e) = case typeOfTerm i ctx e of
    Sid t x y -> Sid t y x
    _ -> error "typeOfTerm.App.Inv"
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeOfTerm i ctx (App InvIdp e) = case typeOfTerm i ctx e of
    t@(Sid _ _ _) ->
        let e' = eval 0 (ctxToCtxV ctx) e
        in Sid (Sid t e' e') (comp 0 (inv 0 e') e') (idp e')
    _ -> error "typeOfTerm.App.InvIdp"
typeOfTerm i ctx (App (App Comp e1) e2) = case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
    (Sid t x _, Sid _ _ z) -> Sid t x z
    _ -> error "typeOfTerm.App.Comp"
typeOfTerm i ctx (App e1 e2) = case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
    (Spi _ _ _ b, _) -> b 0 [] $ eval 0 (ctxToCtxV ctx) e2
    (Sid (Spi _ _ _ t) f g, Sid _ a b) -> Sid (t 0 [] $ error "typeOfTerm.App.Id") (app 0 f a) (app 0 g b)
    _ -> error "typeOfTerm.App"
typeOfTerm i (_,ctx) (LVar v) = ctx `genericIndex` v
typeOfTerm i ctx NoVar = error "typeOfTerm.NoVar"
typeOfTerm i (ctx,_) (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v
    Just (_,t) -> t
typeOfTerm i _ Nat = Stype (Finite 0)
typeOfTerm i _ Suc = Snat `sarr` Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm i _ Rec = eval 0 M.empty $ Pi [(["P"], Pi [([],Nat)] $ Universe Omega)] $
    Pi [([], App (Var "P") $ NatConst 0)] $ Pi [([], iht)] $ Pi [(["x"],Nat)] $ App (Var "P") (Var "x")
  where iht = Pi [(["x"],Nat)] $ Pi [([], App (Var "P") (Var "x"))] $ App (Var "P") $ App Suc (Var "x")
typeOfTerm i ctx (Typed _ t) = eval 0 (ctxToCtxV ctx) t
typeOfTerm i ctx (Ext f g) = Sid (typeOfTerm i ctx f) (eval 0 (ctxToCtxV ctx) f) (eval 0 (ctxToCtxV ctx) g)
typeOfTerm i ctx (ExtSigma p q) = Sid (typeOfTerm i ctx p) (eval 0 (ctxToCtxV ctx) p) (eval 0 (ctxToCtxV ctx) q)
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
               Pi [(["f"],Pi [([],Var "A")] $ Var "B")] $
               Pi [(["g"],Pi [([],Var "B")] $ Var "A")] $
               Pi [([],Pi [(["a"],Var "A")] $ Id (Var "A") (Var "g" `App` (Var "f" `App` Var "a")) (Var "a"))] $
               Pi [([],Pi [(["b"],Var "B")] $ Id (Var "B") (Var "f" `App` (Var "g" `App` Var "b")) (Var "b"))] $
               Id (Universe $ pred $ pred maxBound) (Var "A") (Var "B")
    in eval 0 M.empty term

typeOfLam :: DBIndex -> Ctx -> Term -> Value -> Value -> Value -> Value -> Value
typeOfLam i ctx (Let defs e) t a b p = typeOfLam i (updateCtx ctx defs) e t a b p
typeOfLam i ctx (Lam [] e) t a b p = typeOfLam i ctx e t a b p
typeOfLam i (ctx,lctx) (Lam (x:xs) e) t a b _ = Sid (typeOfTerm i (ctx, (error "typeOfLam.Var", t) : lctx) (Lam xs e)) a b
typeOfLam i ctx e t a b p = case typeOfTerm i ctx e of
    Spi v _ r -> Sid (r 0 [] b) (trans 0 (Slam v r) p a) b
    _ -> error "typeOfLam.Pi"
