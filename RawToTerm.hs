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
    in Lam [v] $ rawExprToTerm (M.insert v (vv, t) ctx) expr' $ Just (s vv)
rawExprToTerm _ (E.Lam _ _ _) _ = error "rawExprToTerm.Lam"
rawExprToTerm ctx (E.Pi [] e) ty = error "rawExprToTerm.Pi"
rawExprToTerm ctx (E.Pi [t] e) ty = rawExprToTerm'depType Pi ctx t e ty
rawExprToTerm ctx (E.Pi (t:ts) e) ty = rawExprToTerm ctx (E.Pi [t] $ E.Pi ts e) ty
rawExprToTerm ctx (E.Sigma [] e) ty = error "rawExprToTerm.Sigma"
rawExprToTerm ctx (E.Sigma [t] e) ty = rawExprToTerm'depType Sigma ctx t e ty
rawExprToTerm ctx (E.Sigma (t:ts) e) ty = rawExprToTerm ctx (E.Sigma [t] $ E.Sigma ts e) ty
rawExprToTerm ctx (E.Arr e1 e2) ty = Pi [([], rawExprToTerm ctx e1 ty)] (rawExprToTerm ctx e2 ty)
rawExprToTerm ctx (E.Prod e1 e2) ty = Sigma [([], rawExprToTerm ctx e1 ty)] (rawExprToTerm ctx e2 ty)
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
rawExprToTerm ctx (E.App e1 e) _ | E.Idp _ <- dropParens e1 = App Idp (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.App e1 e) _ | E.Trans _ <- dropParens e1 = App Trans (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.App e1 e) (Just (Sid (Spi x fv a b) f g)) | E.Ext _ <- dropParens e1 =
    App Ext $ rawExprToTerm ctx e $ Just $ Spi x (fv `union` valueFreeVars f `union` valueFreeVars g) a $
        \v -> Sid (b v) (app 0 f v) (app 0 g v)
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
rawExprToTerm _ (E.Ext _) _ = Ext
rawExprToTerm _ (E.Trans _) _ = Trans
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
typeOfTerm ctx (Id t _ _) = typeOfTerm ctx t
typeOfTerm ctx (App Idp e) =
    let v = eval 0 (ctxToCtxV ctx) e
    in Sid (typeOfTerm ctx e) v v
typeOfTerm ctx (App (App Pmap (App Idp e1)) e2) =
    let e' = eval 0 (ctxToCtxV ctx) e1
    in case typeOfTerm ctx e2 of
        Sid t a b -> Sid (typeOfLam ctx e1 t) (app 0 e' a) (app 0 e' b)
        _ -> error "typeOfTerm.App.App.Pmap.Idp"
typeOfTerm ctx (App (App Pmap e1) e2) =
    case (typeOfTerm ctx e1, typeOfTerm ctx e2) of
        (Sid (Spi _ _ _ b) f g, Sid _ x y) -> Sid (b $ error "typeOfTerm.App.App.Pmap.Var") (app 0 f x) (app 0 g y)
        _ -> error "typeOfTerm.App.App.Pmap"
typeOfTerm ctx (App Trans e) = case typeOfTerm ctx e of
    Sid _ x y -> x `sarr` y
    _ -> error "typeOfTerm.App.Trans"
typeOfTerm ctx (App e1 e2) = case (typeOfTerm ctx e1, typeOfTerm ctx e2) of
    (Spi _ _ _ b, _) -> b $ eval 0 (ctxToCtxV ctx) e2
    (Sid (Spi _ _ _ t) f g, Sid _ a b) -> Sid (t $ error "typeOfTerm.App.Id") (app 0 f a) (app 0 g b)
    _ -> error "typeOfTerm.App"
typeOfTerm ctx (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v
    Just (_,t) -> t
typeOfTerm _ Nat = Stype (Finite 0)
typeOfTerm _ Suc = Snat `sarr` Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm _ Rec = Spi "P" [] (Snat `sarr` Stype maxBound) $ \p ->
    let pfv = valueFreeVars p
    in app 0 p Szero `sarr` (Spi "x" pfv Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" pfv Snat (app 0 p)
typeOfTerm ctx (Typed _ t) = eval 0 (ctxToCtxV ctx) t
typeOfTerm _ (NatConst _) = Snat
typeOfTerm _ (Universe l) = Stype (succ l)
typeOfTerm _ Pmap = error "typeOfTerm.Pmap"
typeOfTerm _ Idp = error "typeOfTerm.Idp"
typeOfTerm _ Ext = error "typeOfTerm.Ext"
typeOfTerm _ Trans = error "typeOfTerm.Trans"

typeOfLam :: Ctx -> Term -> Value -> Value
typeOfLam ctx (Let defs e) a = typeOfLam (updateCtx ctx defs) e a
typeOfLam ctx (Lam [] e) t = typeOfLam ctx e t
typeOfLam ctx (Lam (a:as) e) t = typeOfTerm (M.insert a (svar a t, t) ctx) (Lam as e)
typeOfLam ctx e _ = case typeOfTerm ctx e of
    Spi _ _ _ r -> r $ error "typeOfLam.Var"
    _ -> error "typeOfLam.Pi"
