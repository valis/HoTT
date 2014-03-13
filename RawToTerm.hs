module RawToTerm
    ( evalRaw
    , typeOfTerm
    , rawDefsToTerm, rawExprToTerm
    ) where

import qualified Data.Map as M

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

updateCtx :: Ctx -> [Def] -> Ctx
updateCtx ctx [] = ctx
updateCtx ctx (Def name Nothing expr : ds) =
    updateCtx (M.insert name (eval 0 (ctxToCtxV ctx) expr, typeOfTerm ctx expr) ctx) ds
updateCtx ctx (Def name (Just (ty,args)) expr : ds) =
    updateCtx (M.insert name (eval 0 (ctxToCtxV ctx) (Lam args expr), eval 0 (ctxToCtxV ctx) ty) ctx) ds

rawExprToTerm'depType :: ([([String],Term)] -> Term -> Term) -> Ctx -> [E.TypedVar] -> E.Expr -> Maybe Value -> Term
rawExprToTerm'depType dt ctx tvs e ty = 
    let l = map (\(E.TypedVar _ vars t) -> (exprToVars vars, rawExprToTerm ctx t ty)) tvs
    in dt l $ rawExprToTerm (updateCtx ctx tvs) e ty
  where
    updateCtx ctx [] = ctx
    updateCtx ctx (E.TypedVar _ vars t : tvs) = updateCtx (updateCtxVars ctx $ exprToVars vars) tvs
      where
        tv = evalRaw ctx t ty
        updateCtxVars ctx [] = ctx
        updateCtxVars ctx (v:vs) = updateCtxVars (M.insert v (svar v, tv) ctx) vs

rawExprToTerm :: Ctx -> E.Expr -> Maybe Value -> Term
rawExprToTerm ctx e (Just (Ne (Var "_"))) = rawExprToTerm ctx e Nothing
rawExprToTerm ctx (E.Let defs expr) ty =
    let defs' = rawDefsToTerm ctx defs
    in Let defs' $ rawExprToTerm (updateCtx ctx defs') expr ty
rawExprToTerm ctx (E.Lam _ [] expr) ty = rawExprToTerm ctx expr ty
rawExprToTerm ctx (E.Lam i (arg:args) expr) (Just (Spi _ fv t s)) =
    let (v,expr') = R.renameExpr fv (R.unBinder arg) (E.Lam i args expr)
    in Lam [v] $ rawExprToTerm (M.insert v (svar v, t) ctx) expr' $ Just $ s (svar v)
rawExprToTerm _ (E.Lam _ _ _) _ = error "rawExprToTerm.Lam"
rawExprToTerm ctx (E.Pi tvs e) ty = rawExprToTerm'depType Pi ctx tvs e ty
rawExprToTerm ctx (E.Sigma tvs e) ty = rawExprToTerm'depType Sigma ctx tvs e ty
rawExprToTerm ctx (E.Arr e1 e2) ty = Pi [([], rawExprToTerm ctx e1 ty)] (rawExprToTerm ctx e2 ty)
rawExprToTerm ctx (E.Prod e1 e2) ty = Sigma [([], rawExprToTerm ctx e1 ty)] (rawExprToTerm ctx e2 ty)
rawExprToTerm ctx (E.Id e1 e2) _ =
    let e1' = rawExprToTerm ctx e1 Nothing
    in Id (reify $ typeOfTerm ctx e1') e1' (rawExprToTerm ctx e2 Nothing)
rawExprToTerm ctx (E.App (E.Pmap _ e1) e2) _ = case typeOfTerm ctx (rawExprToTerm ctx e2 Nothing) of
    Sid t _ _ -> let e' = rawExprToTerm ctx e1 $ Just (t `sarr` svar "_")
                 in App (Pmap e') (rawExprToTerm ctx e2 Nothing)
    _ -> error "rawExprToTerm.App.Pmap.Id"
rawExprToTerm ctx (E.App (E.Idp _) e) _ = App Idp (rawExprToTerm ctx e Nothing)
rawExprToTerm ctx (E.App e1 e2) _ =
    let e1' = rawExprToTerm ctx e1 Nothing
    in case typeOfTerm ctx e1' of
        Spi _ _ t2 _ -> App e1' $ rawExprToTerm ctx e2 (Just t2)
        _ -> error "rawExprToTerm.App"
rawExprToTerm ctx (E.Pmap _ e) (Just (Spi _ _ (Sid t _ _) b)) = case b $ error "rawExprToTerm.Pmap.Var" of
    Sid s _ _ -> Pmap $ rawExprToTerm ctx e $ Just (t `sarr` s)
    _ -> error "rawExprToTerm.Pmap.Sid"
rawExprToTerm _ (E.Pmap _ _) _ = error "rawExprToTerm.Pmap.Spi"
rawExprToTerm _ (E.Var a) _ = Var (R.unArg a)
rawExprToTerm _ (E.Nat _) _ = Nat
rawExprToTerm _ (E.Suc _) _ = Suc
rawExprToTerm _ (E.Rec _) _ = Rec
rawExprToTerm _ (E.Idp _) _ = Idp
rawExprToTerm _ (E.NatConst (E.PInt (_,x))) _ = NatConst (read x)
rawExprToTerm _ (E.Universe (E.U (_,x))) _ = Universe (parseLevel x)
rawExprToTerm ctx (E.Paren _ e) ty = rawExprToTerm ctx e ty

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
    updateCtx ctx (v:vs) = updateCtx (M.insert v (svar v, tv) ctx) vs
typeOfTerm ctx (Sigma [] e) = typeOfTerm ctx e
typeOfTerm ctx (Sigma ((vars,t):vs) e) = case (typeOfTerm ctx t, typeOfTerm (updateCtx ctx vars) (Sigma vs e)) of
    (Stype k1, Stype k2) -> Stype (max k1 k2)
    _ -> error "typeOfTerm.Sigma"
  where
    tv = eval 0 (ctxToCtxV ctx) t
    updateCtx ctx [] = ctx
    updateCtx ctx (v:vs) = updateCtx (M.insert v (svar v, tv) ctx) vs
typeOfTerm ctx (Id t _ _) = typeOfTerm ctx t
typeOfTerm ctx (App Idp e) = let t = typeOfTerm ctx e in Spi "x" (valueFreeVars t) t $ \v -> Sid t v v
typeOfTerm ctx (App (Pmap e1) e2) =
    let e' = eval 0 (ctxToCtxV ctx) e1
    in case (typeOfTerm ctx e1, typeOfTerm ctx e2) of
        (Spi x fv t s, Sid _ a b) -> Sid (s $ error "typeOfTerm.Pmap.App.Pi") (app 0 e' a) (app 0 e' b)
        _ -> error "typeOfTerm.Pmap.App"
typeOfTerm ctx (App e1 e2) = case typeOfTerm ctx e1 of
    Spi _ _ _ b -> b $ eval 0 (ctxToCtxV ctx) e2
    _ -> error "typeOfTerm.App"
typeOfTerm ctx (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v ++ " // " ++ show (M.keys ctx)
    Just (_,t) -> t
typeOfTerm _ Nat = Stype (Finite 0)
typeOfTerm _ Suc = Snat `sarr` Snat
typeOfTerm _ Rec = Spi "P" [] (Snat `sarr` Stype maxBound) $ \p ->
    let pfv = valueFreeVars p
    in app 0 p Szero `sarr` (Spi "x" pfv Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" pfv Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm _ (NatConst _) = Snat
typeOfTerm _ (Universe l) = Stype (succ l)
typeOfTerm _ Idp = error "typeOfTerm.Idp"
typeOfTerm _ (Pmap _) = error "typeOfTerm.Pmap"
