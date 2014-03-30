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

updateCtxVar :: M.Map String DBIndex -> Ctx -> [Def] -> (M.Map String DBIndex, Ctx)
updateCtxVar mctx ctx [] = (mctx, ctx)
updateCtxVar mctx actx@(ctx,lctx) (Def name Nothing expr : ds) =
    let t = typeOfTerm 0 actx expr
    in updateCtxVar (M.delete name mctx) (M.insert name (gvar name t, t) ctx, lctx) ds
updateCtxVar mctx actx@(ctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    let t = eval 0 actx ty
    in updateCtxVar (M.delete name mctx) (M.insert name (gvar name t, t) ctx, lctx) ds

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
        (mctx',ctx') = updateCtxVar mctx ctx defs'
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
        t1 = typeOfTerm 0 ctx e1'
    in Id (reifyType i t1) e1' $ rawExprToTerm i mctx ctx e2 (Just t1)
rawExprToTerm i mctx ctx (E.Pmap _) _ = Pmap
rawExprToTerm i mctx ctx (E.App e1 e) _ | E.Pmap _ <- dropParens e1 = App Pmap (rawExprToTerm i mctx ctx e Nothing)
rawExprToTerm i mctx ctx (E.App e1' e2) _
    | E.App e3 e4 <- dropParens e1'
    , E.Pmap _ <- dropParens e3
    , E.App e5 e1 <- dropParens e4
    , E.Idp _ <- dropParens e5 =
        let e2' = rawExprToTerm i mctx ctx e2 Nothing
        in case typeOfTerm 0 ctx e2' of
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
    in case typeOfTerm 0 ctx e1' of
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
