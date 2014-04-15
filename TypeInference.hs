module TypeInference
    ( typeOf
    ) where

import qualified Data.Map as M
import Control.Monad
import Data.List

import TCM
import Eval
import Value
import Syntax.Common
import Syntax.Term

updateCtx :: [Def] -> TCM a -> TCM a
updateCtx [] e = e
updateCtx (Def name Nothing expr : ds) e = do
    t <- typeOf expr
    let upd ctx@(gctx,lctx) = (gctx, (eval 0 (ctxToCtxV ctx) expr, t) : lctx)
    local (\i c mctx ctx -> (i + 1, name : c, M.insert name i mctx, upd ctx)) (updateCtx ds e)
updateCtx (Def name (Just (ty,args)) expr : ds) e =
    let upd ctx@(gctx,lctx) = (gctx, (eval 0 (ctxToCtxV ctx) (Lam args expr), eval 0 (ctxToCtxV ctx) ty) : lctx)
    in local (\i c mctx ctx -> (i + 1, name : c, M.insert name i mctx, upd ctx)) (updateCtx ds e)

updateLCtx :: Value -> [(Value,Value)] -> DBIndex -> DBIndex -> [(Value,Value)]
updateLCtx _ lctx _ 0 = lctx
updateLCtx tv lctx i n = updateLCtx tv ((svar i tv, tv) : lctx) (i + 1) (n - 1)

typeOf :: Term -> TCM Value
typeOf (Let defs e) = updateCtx defs (typeOf e)
typeOf (Lam [] e) = typeOf e
typeOf (Lam _ _) = fail "typeOf.Lam"
typeOf (Pi [] e) = typeOf e
typeOf (Pi ((vars,t):vs) e) = do
    let upd i (gctx,lctx) = (gctx, updateLCtx (eval 0 (ctxToCtxV (gctx,lctx)) t) lctx i $ genericLength vars)
    r <- local (\i c mctx ctx -> (i + genericLength vars, c, mctx, upd i ctx)) $ typeOf (Pi vs e)
    t' <- typeOf t
    case (t',r) of
        (Stype k1, Stype k2) -> return $ Stype (max k1 k2)
        _ -> fail "typeOf.Pi"
typeOf (Sigma [] e) = typeOf e
typeOf (Sigma ((vars,t):vs) e) = do
    let upd i (gctx,lctx) = (gctx, updateLCtx (eval 0 (ctxToCtxV (gctx,lctx)) t) lctx i $ genericLength vars)
    r <- local (\i c mctx ctx -> (i + genericLength vars, c, mctx, upd i ctx)) $ typeOf (Sigma vs e)
    t' <- typeOf t
    case (t',r) of
        (Stype k1, Stype k2) -> return $ Stype (max k1 k2)
        _ -> fail "typeOf.Sigma"
typeOf (Pair e1 e2) = liftM2 (sprod 0) (typeOf e1) (typeOf e2)
typeOf Proj1 = fail "typeOf.Proj1"
typeOf (App Proj1 e) = do
    t <- typeOf e
    case t of
        Ssigma 0 _ a _ -> return a
        _ -> fail "typeOf.App.Proj1"
typeOf Proj2 = fail "typeOf.Proj2"
typeOf (App Proj2 e) = do
    t <- typeOf e
    ctx <- askCtx
    case t of
        Ssigma 0 _ _ b -> return $ b 0 [] $ eval 0 (ctxToCtxV ctx) (App Proj1 e)
        _ -> fail "typeOf.App.Proj1"
typeOf (Id t _ _) = typeOf t
typeOf (App Idp e) = do
    ctx <- askCtx
    let v = eval 0 (ctxToCtxV ctx) e
    t <- typeOf e
    return (Sid 0 t v v)
typeOf (App (App Pmap e1) e2) = do
    t1 <- typeOf e1
    t2 <- typeOf e2
    ctx <- askCtx
    case (t1,t2) of
        (Sid 0 (Spi 0 v _ b) f g, Sid 0 _ x y) ->
            return $ Sid 0 (b 0 [] y) (trans 0 (Slam v b) (eval 0 (ctxToCtxV ctx) e2) (app 0 f x)) (app 0 g y)
        _ -> fail "typeOf.App.App.Pmap"
typeOf (App Coe e) = do
    t <- typeOf e
    case t of
        Sid 0 _ x y -> return (sarr 0 x y)
        _ -> fail "typeOfTerm.App.Coe"
typeOf (App Inv e) = do
    t <- typeOf e
    case t of
        Sid 0 t x y -> return (Sid 0 t y x)
        _ -> fail "typeOf.App.Inv"
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeOf (App InvIdp e) = do
    t <- typeOf e
    ctx <- askCtx
    case t of
        Sid 0 _ _ _ ->
            let e' = eval 0 (ctxToCtxV ctx) e
            in return $ Sid 0 (Sid 0 t e' e') (comp 0 (inv 0 e') e') (idp 0 e')
        _ -> fail "typeOf.App.InvIdp"
typeOf (App (App Comp e1) e2) = do
    t1 <- typeOf e1
    t2 <- typeOf e2
    case (t1,t2) of
        (Sid 0 t x _, Sid 0 _ _ z) -> return (Sid 0 t x z)
        _ -> fail "typeOf.App.Comp"
typeOf (App e1 e2) = do
    t1 <- typeOf e1
    ctx <- askCtx
    case t1 of
        Spi 0 _ _ b -> return $ b 0 [] $ eval 0 (ctxToCtxV ctx) e2
        _ -> fail "typeOf.App"
typeOf (LVar v) = do
    (_,lctx) <- askCtx
    return $ snd $ lctx `genericIndex` v
typeOf NoVar = fail "typeOf.NoVar"
typeOf (Var v) = do
    (gctx,_) <- askCtx
    case M.lookup v gctx of
        Nothing -> fail $ "typeOf.Var: " ++ v
        Just (_,t) -> return t
typeOf Nat = return $ Stype (Finite 0)
typeOf Suc = return (sarr 0 Snat Snat)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOf Rec = return $ eval 0 (M.empty,[]) $ Pi [(["P"], Pi [([],Nat)] $ Universe Omega)] $
    Pi [([], App (LVar 0) $ NatConst 0)] $ Pi [([], iht)] $ Pi [(["x"],Nat)] $ App (LVar 1) (LVar 0)
  where iht = Pi [(["x"],Nat)] $ Pi [([], App (LVar 1) (LVar 0))] $ App (LVar 1) $ App Suc (LVar 0)
typeOf (Ext f g) = do
    t <- typeOf f
    ctx <- askCtx
    return $ Sid 0 t (eval 0 (ctxToCtxV ctx) f) (eval 0 (ctxToCtxV ctx) g)
typeOf (ExtSigma p q) = do
    t <- typeOf p
    ctx <- askCtx
    return $ Sid 0 t (eval 0 (ctxToCtxV ctx) p) (eval 0 (ctxToCtxV ctx) q)
typeOf (NatConst _) = return Snat
typeOf (Universe l) = return $ Stype (succ l)
typeOf Pmap = fail "typeOf.Pmap"
typeOf Idp = fail "typeOf.Idp"
typeOf Coe = fail "typeOf.Coe"
typeOf Comp = fail "typeOf.Comp"
typeOf Inv = fail "typeOf.Inv"
typeOf InvIdp = fail "typeOf.InvIdp"
typeOf Iso = 
    let term = Pi [(["A"],Universe $ pred $ pred maxBound)] $
               Pi [(["B"],Universe $ pred $ pred maxBound)] $
               Pi [(["f"],Pi [([],LVar 1)] $ LVar 0)] $
               Pi [(["g"],Pi [([],LVar 1)] $ LVar 2)] $
               Pi [([],Pi [(["a"],LVar 3)] $ Id (LVar 4) (LVar 1 `App` (LVar 2 `App` LVar 0)) (LVar 0))] $
               Pi [([],Pi [(["b"],LVar 2)] $ Id (LVar 3) (LVar 2 `App` (LVar 1 `App` LVar 0)) (LVar 0))] $
               Id (Universe $ pred $ pred maxBound) (Var "A") (Var "B")
    in return $ eval 0 (M.empty,[]) term
