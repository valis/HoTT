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

evalRaw :: Ctx -> E.Expr -> Maybe Value -> Value
evalRaw ctx e ty = eval 0 (ctxToCtxV ctx) (rawExprToTerm ctx e ty)

rawDefsToTerm :: Ctx -> [E.Def] -> [Def]
rawDefsToTerm ctx [] = []
rawDefsToTerm ctx (E.DefType _ t : E.Def (E.PIdent (_,name)) args e : defs) =
    let t' = rawExprToTerm ctx t Nothing
        e' = rawExprToTerm ctx (E.Lam (error "rawDefsToTerm.Lam") (map E.Binder args) e) $ Just $ eval 0 (ctxToCtxV ctx) t'
    in Def name (Just (t', [])) e' : rawDefsToTerm ctx defs
rawDefsToTerm ctx (E.Def (E.PIdent (_,name)) [] e : defs) =
    Def name Nothing (rawExprToTerm ctx e Nothing) : rawDefsToTerm ctx defs
rawDefsToTerm _ _ = error "rawDefsToTerm"

exprToVars :: E.Expr -> [String]
exprToVars = reverse . go
  where
    go (E.Var (E.NoArg _)) = ["_"]
    go (E.Var (E.Arg (E.PIdent (_,x)))) = [x]
    go (E.App a (E.Var (E.NoArg _))) = "_" : go a
    go (E.App a (E.Var (E.Arg (E.PIdent (_,x))))) = x : go a
    go _ = error "exprToVars"

updateCtxVar :: Ctx -> [Def] -> Ctx
updateCtxVar ctx [] = ctx
updateCtxVar ctx (Def name Nothing expr : ds) =
    let t = typeOfTerm ctx expr
    in updateCtxVar (M.insert name (svar name t, t) ctx) ds
updateCtxVar ctx (Def name (Just (ty,args)) expr : ds) =
    let t = eval 0 (ctxToCtxV ctx) ty
    in updateCtxVar (M.insert name (svar name t, t) ctx) ds

updateCtx :: Ctx -> [Def] -> Ctx
updateCtx ctx [] = ctx
updateCtx ctx (Def name Nothing expr : ds) =
    updateCtx (M.insert name (eval 0 (ctxToCtxV ctx) expr, typeOfTerm ctx expr) ctx) ds
updateCtx ctx (Def name (Just (ty,args)) expr : ds) =
    updateCtx (M.insert name (eval 0 (ctxToCtxV ctx) (Lam args expr), eval 0 (ctxToCtxV ctx) ty) ctx) ds

rawExprToTerm'depType :: ([([String],Term)] -> Term -> Term) -> Ctx -> E.TypedVar -> E.Expr -> Maybe Value -> Term
rawExprToTerm'depType dt ctx (E.TypedVar _ vars t) e ty = 
    dt [(exprToVars vars, rawExprToTerm ctx t ty)] $ rawExprToTerm (updateCtx ctx (exprToVars vars)) e ty
  where
    tv = evalRaw ctx t ty
    updateCtx ctx [] = ctx
    updateCtx ctx (v:vs) = updateCtx (M.insert v (svar v tv, tv) ctx) vs

dropParens :: E.Expr -> E.Expr
dropParens (E.Paren _ e) = dropParens e
dropParens e = e

rawExprToTerm :: Ctx -> E.Expr -> Maybe Value -> Term
rawExprToTerm ctx e (Just (Ne _ (Var "_"))) = rawExprToTerm ctx e Nothing
rawExprToTerm ctx (E.Let defs expr) ty =
    let defs' = rawDefsToTerm ctx defs
    in Let defs' $ rawExprToTerm (updateCtxVar ctx defs') expr ty
rawExprToTerm ctx (E.Lam _ [] expr) ty = rawExprToTerm ctx expr ty
rawExprToTerm ctx (E.Lam i (arg:args) expr) (Just (Spi _ fv t s)) =
    let (v,expr') = R.renameExpr fv (R.unBinder arg) (E.Lam i args expr)
        vv = svar v t
    in Lam [v] $ rawExprToTerm (M.insert v (vv, t) ctx) expr' $ Just (s 0 [] vv)
rawExprToTerm _ (E.Lam _ _ _) _ = error "rawExprToTerm.Lam"
rawExprToTerm ctx (E.Pi [] e) ty = error "rawExprToTerm.Pi"
rawExprToTerm ctx (E.Pi [t] e) ty = rawExprToTerm'depType Pi ctx t e ty
rawExprToTerm ctx (E.Pi (t:ts) e) ty = rawExprToTerm ctx (E.Pi [t] $ E.Pi ts e) ty
rawExprToTerm ctx (E.Sigma [] e) ty = error "rawExprToTerm.Sigma"
rawExprToTerm ctx (E.Sigma [t] e) ty = rawExprToTerm'depType Sigma ctx t e ty
rawExprToTerm ctx (E.Sigma (t:ts) e) ty = rawExprToTerm ctx (E.Sigma [t] $ E.Sigma ts e) ty
rawExprToTerm ctx (E.Arr e1 e2) ty = Pi [([], rawExprToTerm ctx e1 ty)] (rawExprToTerm ctx e2 ty)
rawExprToTerm ctx (E.Prod e1 e2) ty = Sigma [([], rawExprToTerm ctx e1 ty)] (rawExprToTerm ctx e2 ty)
rawExprToTerm ctx (E.Pair e1 e2) (Just (Ssigma _ _ a b)) =
    Pair (rawExprToTerm ctx e1 $ Just a) (rawExprToTerm ctx e2 $ Just $ b 0 [] $ evalRaw ctx e1 $ Just a)
rawExprToTerm ctx (E.Pair e1 e2) (Just _) = error "rawExprToTerm.Pair"
rawExprToTerm ctx (E.Proj1 _) _ = Proj1
rawExprToTerm ctx (E.App e1 e) _ | E.Proj1 _ <- dropParens e1 = App Proj1 (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.Proj2 _) _ = Proj2
rawExprToTerm ctx (E.App e1 e) _ | E.Proj2 _ <- dropParens e1 = App Proj2 (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.Pair e1 e2) Nothing = Pair (rawExprToTerm ctx e1 Nothing) (rawExprToTerm ctx e2 Nothing)
rawExprToTerm ctx (E.Id e1 e2) _ =
    let e1' = rawExprToTerm ctx e1 Nothing
        t1 = typeOfTerm ctx e1'
    in Id (reifyType t1) e1' $ rawExprToTerm ctx e2 (Just t1)
rawExprToTerm ctx (E.Pmap _) _ = Pmap
rawExprToTerm ctx (E.App e1 e) _ | E.Pmap _ <- dropParens e1 = App Pmap (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.App e1' e2) _
    | E.App e3 e4 <- dropParens e1'
    , E.Pmap _ <- dropParens e3
    , E.App e5 e1 <- dropParens e4
    , E.Idp _ <- dropParens e5 =
        let e2' = rawExprToTerm ctx e2 Nothing
        in case typeOfTerm ctx e2' of
            Sid t _ _ -> let e' = rawExprToTerm ctx e1 $ Just $ t `sarr` svar "_" (Stype maxBound)
                         in App (App Pmap (App Idp e')) e2'
            _ -> error "rawExprToTerm.App.App.Idp"
rawExprToTerm ctx (E.App e1' e2) _ | E.App e3 e1 <- dropParens e1', E.Pmap _ <- dropParens e3 =
    App (App Pmap (rawExprToTerm ctx e1 Nothing)) (rawExprToTerm ctx e2 Nothing)
rawExprToTerm ctx (E.App e1 e) (Just (Sid t _ _)) | E.Idp _ <- dropParens e1 = App Idp $ rawExprToTerm ctx e (Just t)
rawExprToTerm ctx (E.App e1 e) (Just _) | E.Idp _ <- dropParens e1 = error "rawExrToTerm.App.Idp"
rawExprToTerm ctx (E.App e1 e) Nothing | E.Idp _ <- dropParens e1 = App Idp (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.App e1 e) _ | E.Coe _ <- dropParens e1 = App Coe (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.App e1 e) (Just (Sid t@(Spi x fv a b) f g)) | E.Ext _ <- dropParens e1 =
    App (Ext (reify f t) (reify g t)) $ rawExprToTerm ctx e $ Just $
    Spi x (fv `union` valueFreeVars f `union` valueFreeVars g) a $ \k m v ->
        let r1 = b k m v
            r2 = app k (action m f) v 
            r3 = app k (action m g) v
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)]) $ Id (Var "r1") (Var "r2") (Var "r3")
rawExprToTerm ctx (E.App e1 e) (Just (Sid t@(Ssigma x fv a b) p q)) | E.Ext _ <- dropParens e1 =
    App (ExtSigma (reify p t) (reify q t)) $ rawExprToTerm ctx e $ Just $
    Ssigma x (fv `union` valueFreeVars p `union` valueFreeVars q) (Sid a (proj1 p) (proj1 q)) $ \k m v ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x fv b) v (action m $ proj2 p)
            r3 = proj2 q
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)]) $ Id (Var "r1") (Var "r2") (Var "r3")
rawExprToTerm _ (E.Ext _) (Just (Spi _ _ a b)) = case b 0 [] (error "rawExprToTerm.Ext.Var") of
    Sid t@(Spi _ _ _ _) f g -> Ext (reify f t) (reify g t)
    Sid t@(Ssigma _ _ _ _) p q -> ExtSigma (reify p t) (reify q t)
    _ -> error "rawExprToTerm.Ext.Pi"
rawExprToTerm _ (E.Ext _) _ = error "rawExprToTerm.Ext"
rawExprToTerm ctx (E.App e1 e2) _ =
    let e1' = rawExprToTerm ctx e1 Nothing
    in case typeOfTerm ctx e1' of
        Spi _ _ t2 _ -> App e1' $ rawExprToTerm ctx e2 (Just t2)
        Sid _ _ _ -> App e1' (rawExprToTerm ctx e2 Nothing)
        _ -> error "rawExprToTerm.App"
rawExprToTerm _ (E.Var a) _ = Var (R.unArg a)
rawExprToTerm _ (E.Nat _) _ = Nat
rawExprToTerm _ (E.Suc _) _ = Suc
rawExprToTerm _ (E.Rec _) _ = Rec
rawExprToTerm _ (E.Idp _) _ = Idp
rawExprToTerm _ (E.Coe _) _ = Coe
rawExprToTerm _ (E.NatConst (E.PInt (_,x))) _ = NatConst (read x)
rawExprToTerm _ (E.Universe (E.U (_,x))) _ = Universe (parseLevel x)
rawExprToTerm ctx (E.Paren _ e) ty = rawExprToTerm ctx e ty
rawExprToTerm ctx (E.Typed e1 e2) _ =
    let e2' = rawExprToTerm ctx e2 $ Just (Stype maxBound)
    in Typed (rawExprToTerm ctx e1 $ Just $ eval 0 (ctxToCtxV ctx) e2') e2'

typeOfTerm :: Ctx -> Term -> Value
typeOfTerm ctx (Let defs e) = typeOfTerm (updateCtx ctx defs) e
typeOfTerm ctx (Lam [] e) = typeOfTerm ctx e
typeOfTerm _ (Lam _ _) = error "typeOfTerm.Lam"
typeOfTerm ctx (Pi [] e) = typeOfTerm ctx e
typeOfTerm ctx (Pi ((vars,t):vs) e) = case (typeOfTerm ctx t, typeOfTerm (updateCtx ctx vars) (Pi vs e)) of
    (Stype k1, Stype k2) -> Stype (max k1 k2)
    _ -> error "typeOfTerm.Pi"
  where
    tv = eval 0 (ctxToCtxV ctx) t
    updateCtx ctx [] = ctx
    updateCtx ctx (v:vs) = updateCtx (M.insert v (svar v tv, tv) ctx) vs
typeOfTerm ctx (Sigma [] e) = typeOfTerm ctx e
typeOfTerm ctx (Sigma ((vars,t):vs) e) = case (typeOfTerm ctx t, typeOfTerm (updateCtx ctx vars) (Sigma vs e)) of
    (Stype k1, Stype k2) -> Stype (max k1 k2)
    _ -> error "typeOfTerm.Sigma"
  where
    tv = eval 0 (ctxToCtxV ctx) t
    updateCtx ctx [] = ctx
    updateCtx ctx (v:vs) = updateCtx (M.insert v (svar v tv, tv) ctx) vs
typeOfTerm ctx (Pair e1 e2) = typeOfTerm ctx e1 `sprod` typeOfTerm ctx e2
typeOfTerm ctx Proj1 = error "typeOfTerm.Proj1"
typeOfTerm ctx (App Proj1 e) = case typeOfTerm ctx e of
    Ssigma _ _ a _ -> a
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm ctx Proj2 = error "typeOfTerm.Proj2"
typeOfTerm ctx (App Proj2 e) = case typeOfTerm ctx e of
    Ssigma _ _ _ b -> b 0 [] $ eval 0 (ctxToCtxV ctx) (App Proj1 e)
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm ctx (Id t _ _) = typeOfTerm ctx t
typeOfTerm ctx (App Idp e) =
    let v = eval 0 (ctxToCtxV ctx) e
    in Sid (typeOfTerm ctx e) v v
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfTerm ctx (App (App Pmap (App Idp e1)) e2) =
    let e' = eval 0 (ctxToCtxV ctx) e1
    in case typeOfTerm ctx e2 of
        Sid t a b -> typeOfLam ctx e1 t (app 0 e' a) (app 0 e' b) (eval 0 (ctxToCtxV ctx) e2)
        _ -> error "typeOfTerm.App.App.Pmap.Idp"
typeOfTerm ctx (App (App Pmap e1) e2) =
    case (typeOfTerm ctx e1, typeOfTerm ctx e2) of
        (Sid (Spi v fv _ b) f g, Sid _ x y) ->
            Sid (b 0 [] y) (trans 0 (Slam v fv b) (eval 0 (ctxToCtxV ctx) e2) (app 0 f x)) (app 0 g y)
        _ -> error "typeOfTerm.App.App.Pmap"
typeOfTerm ctx (App Coe e) = case typeOfTerm ctx e of
    Sid _ x y -> x `sarr` y
    _ -> error "typeOfTerm.App.Coe"
typeOfTerm ctx (App e1 e2) = case (typeOfTerm ctx e1, typeOfTerm ctx e2) of
    (Spi _ _ _ b, _) -> b 0 [] $ eval 0 (ctxToCtxV ctx) e2
    (Sid (Spi _ _ _ t) f g, Sid _ a b) -> Sid (t 0 [] $ error "typeOfTerm.App.Id") (app 0 f a) (app 0 g b)
    _ -> error "typeOfTerm.App"
typeOfTerm ctx (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v
    Just (_,t) -> t
typeOfTerm _ Nat = Stype (Finite 0)
typeOfTerm _ Suc = Snat `sarr` Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm _ Rec = eval 0 M.empty $ Pi [(["P"], Pi [([],Nat)] $ Universe Omega)] $
    Pi [([], App (Var "P") $ NatConst 0)] $ Pi [([], iht)] $ Pi [(["x"],Nat)] $ App (Var "P") (Var "x")
  where iht = Pi [(["x"],Nat)] $ Pi [([], App (Var "P") (Var "x"))] $ App (Var "P") $ App Suc (Var "x")
typeOfTerm ctx (Typed _ t) = eval 0 (ctxToCtxV ctx) t
typeOfTerm ctx (Ext f g) = Sid (typeOfTerm ctx f) (eval 0 (ctxToCtxV ctx) f) (eval 0 (ctxToCtxV ctx) g)
typeOfTerm ctx (ExtSigma p q) = Sid (typeOfTerm ctx p) (eval 0 (ctxToCtxV ctx) p) (eval 0 (ctxToCtxV ctx) q)
typeOfTerm _ (NatConst _) = Snat
typeOfTerm _ (Universe l) = Stype (succ l)
typeOfTerm _ Pmap = error "typeOfTerm.Pmap"
typeOfTerm _ Idp = error "typeOfTerm.Idp"
typeOfTerm _ Coe = error "typeOfTerm.Coe"

typeOfLam :: Ctx -> Term -> Value -> Value -> Value -> Value -> Value
typeOfLam ctx (Let defs e) t a b p = typeOfLam (updateCtx ctx defs) e t a b p
typeOfLam ctx (Lam [] e) t a b p = typeOfLam ctx e t a b p
typeOfLam ctx (Lam (x:xs) e) t a b _ = Sid (typeOfTerm (M.insert x (error "typeOfLam.Var", t) ctx) (Lam xs e)) a b
typeOfLam ctx e t a b p = case typeOfTerm ctx e of
    Spi v fv _ r -> Sid (r 0 [] b) (trans 0 (Slam v fv r) p a) b
    _ -> error "typeOfLam.Pi"
