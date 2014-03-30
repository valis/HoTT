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
evalRaw i mctx ctx e ty = eval 0 ctx (rawExprToTerm i mctx ctx e ty)

rawDefsToTerm :: DBIndex -> M.Map String DBIndex -> Ctx -> [E.Def] -> [Def]
rawDefsToTerm i mctx ctx [] = []
rawDefsToTerm i mctx ctx (E.DefType _ t : E.Def (E.PIdent (_,name)) args e : defs) =
    let t' = rawExprToTerm i mctx ctx t Nothing
        e' = rawExprToTerm i mctx ctx (E.Lam (error "rawDefsToTerm.Lam") (map E.Binder args) e) $
            Just $ eval 0 ctx t'
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
updateCtxVar i mctx actx@(ctx,lctx) (Def name Nothing expr : ds) =
    let t = typeOfTerm i actx expr
    in updateCtxVar i (M.delete name mctx) (M.insert name (gvar name t, t) ctx, lctx) ds
updateCtxVar i mctx actx@(ctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    let t = eval 0 actx ty
    in updateCtxVar i (M.delete name mctx) (M.insert name (gvar name t, t) ctx, lctx) ds

updateCtx :: DBIndex -> Ctx -> [Def] -> Ctx
updateCtx _ ctx [] = ctx
updateCtx i actx@(ctx,lctx) (Def name Nothing expr : ds) =
    updateCtx i (M.insert name (eval 0 actx expr, typeOfTerm i actx expr) ctx, lctx) ds
updateCtx i actx@(ctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    updateCtx i (M.insert name (eval 0 actx (Lam args expr), eval 0 actx ty) ctx, lctx) ds

rawExprToTerm'depType :: ([([String],Term)] -> Term -> Term) -> DBIndex
    -> M.Map String DBIndex -> Ctx -> E.TypedVar -> E.Expr -> Maybe Value -> Term
rawExprToTerm'depType dt i mctx (ctx,lctx) (E.TypedVar _ vars t) e ty =
    let vars' = exprToVars vars
        l = genericLength vars'
    in dt [(vars', rawExprToTerm i mctx (ctx,lctx) t ty)] $
        rawExprToTerm (i + l) (updateCtx mctx i vars') (ctx, updateLCtx lctx i l) e ty
  where
    tv = evalRaw i mctx (ctx,lctx) t ty
    updateCtx mctx i [] = mctx
    updateCtx mctx i (v:vs) = updateCtx (M.insert v i mctx) (i + 1) vs
    updateLCtx lctx _ 0 = lctx
    updateLCtx lctx i n = updateLCtx ((svar i tv, tv) : lctx) (i + 1) (n - 1)

dropParens :: E.Expr -> E.Expr
dropParens (E.Paren _ e) = dropParens e
dropParens e = e

rawExprToTerm :: DBIndex -> M.Map String DBIndex -> Ctx -> E.Expr -> Maybe Value -> Term
rawExprToTerm i mctx ctx e (Just (Ne _ t)) | NoVar <- t 0 = rawExprToTerm i mctx ctx e Nothing
rawExprToTerm i mctx ctx (E.Let defs expr) ty =
    let defs' = rawDefsToTerm i mctx ctx defs
        (mctx',ctx') = updateCtxVar i mctx ctx defs'
    in Let defs' (rawExprToTerm i mctx' ctx' expr ty)
rawExprToTerm i mctx ctx (E.Lam _ [] expr) ty = rawExprToTerm i mctx ctx expr ty
rawExprToTerm i mctx (ctx,lctx) (E.Lam j (arg:args) expr) (Just (Spi _ t s)) =
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
rawExprToTerm i mctx ctx (E.Pair e1 e2) (Just (Ssigma _ a b)) =
    Pair (rawExprToTerm i mctx ctx e1 $ Just a)
         (rawExprToTerm i mctx ctx e2 $ Just $ b 0 [] $ evalRaw i mctx ctx e1 $ Just a)
rawExprToTerm i _ _ (E.Pair e1 e2) (Just _) = error "rawExprToTerm.Pair"
rawExprToTerm i _ _ (E.Proj1 _) _ = Proj1
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Proj1 _ <- dropParens e1 = App Proj1 (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i _ _ (E.Proj2 _) _ = Proj2
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Proj2 _ <- dropParens e1 = App Proj2 (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.Pair e1 e2) Nothing =
    Pair (rawExprToTerm i mctx ctx e1 Nothing) (rawExprToTerm i mctx ctx e2 Nothing)
rawExprToTerm i mctx ctx (E.Id e1 e2) _ =
    let e1' = rawExprToTerm i mctx ctx e1 Nothing
        t1 = typeOfTerm i ctx e1'
    in Id (reifyType i t1) e1' $ rawExprToTerm i mctx ctx e2 (Just t1)
rawExprToTerm i mctx ctx (E.Pmap _) _ = Pmap
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Pmap _ <- dropParens e1 = App Pmap (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1' e2) _
    | E.App e3 e4 <- dropParens e1'
    , E.Pmap _ <- dropParens e3
    , E.App e5 e1 <- dropParens e4
    , E.Idp _ <- dropParens e5 =
        let e2' = rawExprToTerm i mctx ctx e2 Nothing
        in case typeOfTerm i ctx e2' of
            Sid t _ _ -> let e' = rawExprToTerm i mctx ctx e1 $ Just $ t `sarr` Ne [] (const NoVar)
                         in App (App Pmap (App Idp e')) e2'
            _ -> error "rawExprToTerm.App.App.Idp"
rawExprToTerm i mctx ctx (E.App e1' e2) _ | E.App e3 e1 <- dropParens e1', E.Pmap _ <- dropParens e3 =
    App (App Pmap (rawExprToTerm i mctx ctx e1 Nothing)) (rawExprToTerm i mctx ctx e2 Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid t _ _)) | E.Idp _ <- dropParens e1 =
    App Idp $ rawExprToTerm i mctx ctx e (Just t)
rawExprToTerm i _ _ (E.App e1 e) (Just _) | E.Idp _ <- dropParens e1 = error "rawExprToTerm.App.Idp"
rawExprToTerm i mctx ctx (E.App e1 e) Nothing | E.Idp _ <- dropParens e1 = App Idp (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Coe _ <- dropParens e1 = App Coe (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid t@(Spi x a b) f g)) | E.Ext _ <- dropParens e1 =
    App (Ext (reify i f t) (reify i g t)) $ rawExprToTerm i mctx ctx e $ Just $
    Spi x a $ \k m v ->
        let r1 = b k m v
            r2 = app k (action m f) v 
            r3 = app k (action m g) v
        in eval k (M.fromList [("r1",(r1,Stype maxBound)),("r2",(r2,r1)),("r3",(r3,r1))], []) $ Id (Var "r1") (Var "r2") (Var "r3")
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid t@(Ssigma x a b) p q)) | E.Ext _ <- dropParens e1 =
    App (ExtSigma (reify i p t) (reify i q t)) $ rawExprToTerm i mctx ctx e $ Just $
    Ssigma x (Sid a (proj1 p) (proj1 q)) $ \k m v ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x b) v (action m $ proj2 p)
            r3 = proj2 q
        in eval k (M.fromList [("r1",(r1,Stype maxBound)),("r2",(r2,r1)),("r3",(r3,r1))], []) $ Id (Var "r1") (Var "r2") (Var "r3")
rawExprToTerm i _ _ (E.Ext _) (Just (Spi _ a b)) = case b 0 [] (error "rawExprToTerm.Ext.Var") of
    Sid t@(Spi _ _ _) f g -> Ext (reify i f t) (reify i g t)
    Sid t@(Ssigma _ _ _) p q -> ExtSigma (reify i p t) (reify i q t)
    _ -> error "rawExprToTerm.Ext.Pi"
rawExprToTerm i _ _ (E.Ext _) _ = error "rawExprToTerm.Ext"
rawExprToTerm i mctx ctx (E.App e1 e) (Just (Sid t x y)) | E.Inv _ <- dropParens e1 =
    App Inv $ rawExprToTerm i mctx ctx e $ Just (Sid t y x)
rawExprToTerm i _ _ (E.App e1 e) (Just _) | E.Inv _ <- dropParens e1 = error "rawExprToTerm.App.Inv"
rawExprToTerm i mctx ctx (E.App e1 e) Nothing | E.Inv _ <- dropParens e1 = App Inv (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.InvIdp _ <- dropParens e1 = App InvIdp (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1' e2) _ | E.App e3 e1 <- dropParens e1', E.Comp _ <- dropParens e3 =
    Comp `App` rawExprToTerm i mctx ctx e1 Nothing `App` rawExprToTerm i mctx ctx e2 Nothing
rawExprToTerm i mctx ctx (E.App e1 e2) _ =
    let e1' = rawExprToTerm i mctx ctx e1 Nothing
    in case typeOfTerm i ctx e1' of
        Spi _ t2 _ -> App e1' $ rawExprToTerm i mctx ctx e2 (Just t2)
        Sid _ _ _ -> App e1' (rawExprToTerm i mctx ctx e2 Nothing)
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
    in Typed (rawExprToTerm i mctx ctx e1 $ Just $ eval 0 ctx e2') e2'

updateLCtx :: DBIndex -> Value -> [(Value,Value)] -> [String] -> [(Value,Value)]
updateLCtx _ tv lctx [] = lctx
updateLCtx i tv lctx (_:vs) = updateLCtx (i + 1) tv ((svar i tv, tv) : lctx) vs

typeOfTerm :: DBIndex -> Ctx -> Term -> Value
typeOfTerm i ctx (Let defs e) = typeOfTerm i (updateCtx i ctx defs) e
typeOfTerm i ctx (Lam [] e) = typeOfTerm i ctx e
typeOfTerm _ _ (Lam _ _) = error "typeOfTerm.Lam"
typeOfTerm i ctx (Pi [] e) = typeOfTerm i ctx e
typeOfTerm i (ctx,lctx) (Pi ((vars,t):vs) e) =
    let r = typeOfTerm (i + genericLength vars) (ctx, updateLCtx i (eval 0 (ctx,lctx) t) lctx vars) (Pi vs e)
    in case (typeOfTerm i (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Pi"
typeOfTerm i ctx (Sigma [] e) = typeOfTerm i ctx e
typeOfTerm i (ctx,lctx) (Sigma ((vars,t):vs) e) =
    let r = typeOfTerm (i + genericLength vars) (ctx, updateLCtx i (eval 0 (ctx,lctx) t) lctx vars) (Sigma vs e)
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
    Ssigma _ _ b -> b 0 [] $ eval 0 ctx (App Proj1 e)
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm i ctx (Id t _ _) = typeOfTerm i ctx t
typeOfTerm i ctx (App Idp e) =
    let v = eval 0 ctx e
    in Sid (typeOfTerm i ctx e) v v
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfTerm i ctx (App (App Pmap (App Idp e1)) e2) =
    let e' = eval 0 ctx e1
    in case typeOfTerm i ctx e2 of
        Sid t a b -> typeOfLam i ctx e1 t (app 0 e' a) (app 0 e' b) (eval 0 ctx e2)
        _ -> error "typeOfTerm.App.App.Pmap.Idp"
typeOfTerm i ctx (App (App Pmap e1) e2) =
    case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
        (Sid (Spi v _ b) f g, Sid _ x y) ->
            Sid (b 0 [] y) (trans 0 (Slam v b) (eval 0 ctx e2) (app 0 f x)) (app 0 g y)
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
        let e' = eval 0 ctx e
        in Sid (Sid t e' e') (comp 0 (inv 0 e') e') (idp 0 e')
    _ -> error "typeOfTerm.App.InvIdp"
typeOfTerm i ctx (App (App Comp e1) e2) = case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
    (Sid t x _, Sid _ _ z) -> Sid t x z
    _ -> error "typeOfTerm.App.Comp"
typeOfTerm i ctx (App e1 e2) = case (typeOfTerm i ctx e1, typeOfTerm i ctx e2) of
    (Spi _ _ b, _) -> b 0 [] $ eval 0 ctx e2
    (Sid (Spi _ _ t) f g, Sid _ a b) -> Sid (t 0 [] $ error "typeOfTerm.App.Id") (app 0 f a) (app 0 g b)
    _ -> error "typeOfTerm.App"
typeOfTerm _ (_,ctx) (LVar v) = snd $ ctx `genericIndex` v
typeOfTerm i ctx NoVar = error "typeOfTerm.NoVar"
typeOfTerm i (ctx,_) (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v
    Just (_,t) -> t
typeOfTerm i _ Nat = Stype (Finite 0)
typeOfTerm i _ Suc = Snat `sarr` Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm i _ Rec = eval 0 (M.empty,[]) $ Pi [(["P"], Pi [([],Nat)] $ Universe Omega)] $
    Pi [([], App (LVar 0) $ NatConst 0)] $ Pi [([], iht)] $ Pi [(["x"],Nat)] $ App (LVar 1) (LVar 0)
  where iht = Pi [(["x"],Nat)] $ Pi [([], App (LVar 1) (LVar 0))] $ App (LVar 1) $ App Suc (LVar 0)
typeOfTerm i ctx (Typed _ t) = eval 0 ctx t
typeOfTerm i ctx (Ext f g) = Sid (typeOfTerm i ctx f) (eval 0 ctx f) (eval 0 ctx g)
typeOfTerm i ctx (ExtSigma p q) = Sid (typeOfTerm i ctx p) (eval 0 ctx p) (eval 0 ctx q)
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
               Pi [([],Pi [(["a"],LVar 3)] $ Id (LVar 4) (LVar 1 `App` (LVar 2 `App` LVar 0)) (LVar 0))] $
               Pi [([],Pi [(["b"],LVar 2)] $ Id (LVar 3) (LVar 2 `App` (LVar 1 `App` LVar 0)) (LVar 0))] $
               Id (Universe $ pred $ pred maxBound) (Var "A") (Var "B")
    in eval 0 (M.empty,[]) term

typeOfLam :: DBIndex -> Ctx -> Term -> Value -> Value -> Value -> Value -> Value
typeOfLam i ctx (Let defs e) t a b p = typeOfLam i (updateCtx i ctx defs) e t a b p
typeOfLam i ctx (Lam [] e) t a b p = typeOfLam i ctx e t a b p
typeOfLam i (ctx,lctx) (Lam (x:xs) e) t a b _ = Sid (typeOfTerm i (ctx, (error "typeOfLam.Var", t) : lctx) (Lam xs e)) a b
typeOfLam i ctx e t a b p = case typeOfTerm i ctx e of
    Spi v _ r -> Sid (r 0 [] b) (trans 0 (Slam v r) p a) b
    _ -> error "typeOfLam.Pi"
