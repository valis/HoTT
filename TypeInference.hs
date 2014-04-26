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
import Cube

updateCtx :: [Def] -> TCM a -> TCM a
updateCtx [] e = e
updateCtx (Def name Nothing expr : ds) e = do
    t <- typeOf expr
    let upd ctx@(gctx,lctx) = (gctx, (eval 0 (ctxToCtxV ctx) expr, t) : lctx)
    local (\i c mctx ctx -> (i + 1, name : c, M.insert name i mctx, upd ctx)) (updateCtx ds e)
updateCtx (Def name (Just (ty,args)) expr : ds) e =
    let upd ctx@(gctx,lctx) = (gctx, (eval 0 (ctxToCtxV ctx) (Lam 0 args expr), eval 0 (ctxToCtxV ctx) ty) : lctx)
    in local (\i c mctx ctx -> (i + 1, name : c, M.insert name i mctx, upd ctx)) (updateCtx ds e)

updateLCtx :: Value -> [(Value,Value)] -> DBIndex -> DBIndex -> [(Value,Value)]
updateLCtx _ lctx _ 0 = lctx
updateLCtx tv lctx i n = updateLCtx tv ((svar i 0 tv, tv) : lctx) (i + 1) (n - 1)

typeOf :: Term -> TCM Value
typeOf (Let defs e) = updateCtx defs (typeOf e)
typeOf (Lam _ [] e) = typeOf e
typeOf (Lam _ _ _) = fail "typeOf.Lam"
typeOf (Pi _ [] e) = typeOf e
typeOf (Pi n ((vars,t):vs) e) = do
    let upd i (gctx,lctx) = (gctx, updateLCtx (eval 0 (ctxToCtxV (gctx,lctx)) t) lctx i $ genericLength vars)
    r <- local (\i c mctx ctx -> (i + genericLength vars, c, mctx, upd i ctx)) $ typeOf (Pi n vs e)
    t' <- typeOf t
    case (t',r) of
        (Stype k1, Stype k2) -> return $ Stype (max k1 k2)
        _ -> fail "typeOf.Pi"
typeOf (Sigma _ [] e) = typeOf e
typeOf (Sigma n ((vars,t):vs) e) = do
    let upd i (gctx,lctx) = (gctx, updateLCtx (eval 0 (ctxToCtxV (gctx,lctx)) t) lctx i $ genericLength vars)
    r <- local (\i c mctx ctx -> (i + genericLength vars, c, mctx, upd i ctx)) $ typeOf (Sigma n vs e)
    t' <- typeOf t
    case (t',r) of
        (Stype k1, Stype k2) -> return $ Stype (max k1 k2)
        _ -> fail "typeOf.Sigma"
typeOf (Pair e1 e2) = liftM2 sprod (typeOf e1) (typeOf e2)
typeOf Proj1 = fail "typeOf.Proj1"
typeOf (App _ Proj1 e) = do
    t <- typeOf e
    case t of
        Ssigma a _ -> return a
        _ -> fail "typeOf.App.Proj1"
typeOf Proj2 = fail "typeOf.Proj2"
typeOf (App _ Proj2 e) = do
    t <- typeOf e
    ctx <- askCtx
    case t of
        Ssigma _ b -> return $ app 0 b $ eval 0 (ctxToCtxV ctx) (App 0 Proj1 e)
        _ -> fail "typeOf.App.Proj1"
typeOf (Id _ t _ _) = do
    Sid r _ _ <- typeOf t
    return r
typeOf (App _ Idp e) = do
    ctx <- askCtx
    let v = eval 0 (ctxToCtxV ctx) e
    t <- typeOf e
    return (Sid (action (cubeMapd $ degMap [False]) t) v v)
typeOf (Pmap e1 e2) = do
    t1 <- typeOf e1
    t2 <- typeOf e2
    ctx <- askCtx
    case (t1,t2) of
        (Sid (Spi _ b@(Slam v _)) f g, Sid _ x y) ->
            return $ Sid (app 1 b $ unPath $ eval 0 (ctxToCtxV ctx) e2) (app 0 f x) (app 0 g y)
        _ -> fail "typeOf.App.App.Pmap"
typeOf (App _ Coe e) = do
    t <- typeOf e
    case t of
        Sid _ x y -> return (sarr x y)
        _ -> fail "typeOfTerm.App.Coe"
typeOf (App _ e1 e2) = do
    t1 <- typeOf e1
    ctx <- askCtx
    case t1 of
        Spi _ b -> return $ app 0 b $ eval 0 (ctxToCtxV ctx) e2
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
typeOf Suc = return (sarr Snat Snat)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOf Rec = return $ eval 0 (M.empty,[]) $ Pi 0 [(["P"], Pi 0 [([],Nat)] $ Universe Omega)] $
    Pi 0 [([], App 0 (LVar 0) $ NatConst 0)] $ Pi 0 [([], iht)] $ Pi 0 [(["x"],Nat)] $ App 0 (LVar 1) (LVar 0)
  where iht = Pi 0 [(["x"],Nat)] $ Pi 0 [([], App 0 (LVar 1) (LVar 0))] $ App 0 (LVar 1) $ App 0 Suc (LVar 0)
typeOf (NatConst _) = return Snat
typeOf (Universe l) = return $ Stype (succ l)
typeOf (Act _ _) = fail "typeOf.Act"
typeOf (Comp _ _ _) = fail "typeOf.Comp"
typeOf Idp = fail "typeOf.Idp"
typeOf Coe = fail "typeOf.Coe"
typeOf Pcon = fail "typeOf.Pcon"
typeOf Iso = 
    let term = Pi 0 [(["A"],Universe $ pred $ pred maxBound)] $
               Pi 0 [(["B"],Universe $ pred $ pred maxBound)] $
               Pi 0 [(["f"],Pi 0 [([],LVar 1)] $ LVar 0)] $
               Pi 0 [(["g"],Pi 0 [([],LVar 1)] $ LVar 2)] $
               Pi 0 [([],Pi 0 [(["a"],LVar 3)] $ Id 0 (App 0 Idp $ LVar 4) (App 0 (LVar 1) (App 0 (LVar 2) $ LVar 0)) (LVar 0))] $
               Pi 0 [([],Pi 0 [(["b"],LVar 2)] $ Id 0 (App 0 Idp $ LVar 3) (App 0 (LVar 2) (App 0 (LVar 1) $ LVar 0)) (LVar 0))] $
               Id 0 (App 0 Idp $ Universe $ pred $ pred maxBound) (Var "A") (Var "B")
    in return $ eval 0 (M.empty,[]) term
