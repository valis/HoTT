module Eval
    ( eval
    , typeOfTerm
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Control.Arrow((***))

import Syntax.Common
import Syntax.Term
import Value

eval :: Integer -> Ctx -> Term -> Value
-- iso A B f g
-- pmap (\A -> idp (iso A B f g)) (p : A1 = A2)
--   : iso A1 B (\a -> f (coe (inv p) a)) (\b -> coe (inv p) (g b)) = iso A2 B (f : A2 -> B) (g : B -> A2)
-- pmap (\A -> idp (iso A A (\x -> x) (\x -> x))) (p : A1 = A2)
--   : iso A2 A2 (\x -> coe p (coe (inv p) x)) (\x -> coe p (coe (inv p) x)) = iso A2 A2 (\x -> x) (\x -> x)
{-
eval _ _ Iso = Slam "A" $ \_  _  va ->
               Slam "B" $ \_  mb vb ->
               Slam "f" $ \_  mf vf ->
               Slam "g" $ \_  mg vg ->
               Slam "p" $ \_  mp vp ->
               Slam "q" $ \kq mq vq ->
    Siso kq (error "TODO: eval.Iso.1") (error "TODO: eval.Iso.2") (error "TODO: eval.Iso.3")
            (error "TODO: eval.Iso.4") (error "TODO: eval.Iso.5") (error "TODO: eval.Iso.6")
-}
eval _ _ Iso = error "TODO: eval.Iso"
eval _ _ Comp = Slam "p" $ \_ _ p -> Slam "q" $ \k m -> comp k (action m p)
eval _ _ Inv = Slam "p" $ \k _ -> inv k
eval _ _ InvIdp = Slam "p" $ \k _ -> invIdp k
eval _ _ Idp = Slam "x" $ \k _ -> idp k
eval _ _ Coe = Slam "p" $ \_ _ -> coe
-- pmap : {f g : (a : A) -> B a} -> f = g -> (p : a = a') -> transport B p (f a) = g a'
eval _ _ Pmap = Slam "p" $ \_ _ p -> Slam "q" $ \k _ -> pmap k p
-- ext : ((x : A) -> f x = g x) -> f = g
eval n (ctx,lctx) (Ext f g) = Slam "h" $ \_ n h -> Slam "p" $ \k m p -> case (k,lastD m) of
    (0,Just Ld) -> eval 0 (M.map (action (n ++ m) *** action (n ++ m)) ctx, map (action (n ++ m) *** action (n ++ m)) lctx) f
    (0,Just Rd) -> eval 0 (M.map (action (n ++ m) *** action (n ++ m)) ctx, map (action (n ++ m) *** action (n ++ m)) lctx) g
    (0,_) -> error "eval.Ext"
    _ -> comp (k - 1) (app (k - 1) (action m h) $ action [Ld] p)
                      (app k (eval k (M.map (action (n ++ m ++ [Ud]) *** action (n ++ m ++ [Ud])) ctx, map (action (n ++ m ++ [Ud]) *** action (n ++ m ++ [Ud])) lctx) g) p)
eval n ctx (ExtSigma _ _) = idf
eval n ctx (Pair e1 e2) = Spair (eval n ctx e1) (eval n ctx e2)
eval n ctx Proj1 = Slam "p" $ \_ _ -> proj1
eval n ctx Proj2 = Slam "p" $ \_ _ -> proj2
eval n ctx (Let [] e) = eval n ctx e
eval n (ctx,lctx) (Let (Def v Nothing d : ds) e) = eval n (M.insert v (eval n (ctx,lctx) d, error "TODO: eval.Let") ctx, lctx) (Let ds e)
eval n (ctx,lctx) (Let (Def v (Just (t,args)) d : ds) e) =
    eval n (M.insert v (eval n (ctx,lctx) $ Lam args d, eval n (ctx,lctx) t) ctx, lctx) (Let ds e)
eval n ctx (Lam args e) = go n ctx args -- TODO: Fix this.
  where
    go n ctx []     = eval n ctx e
    go n (ctx,lctx) s@(a:as) = Slam a $ \k m v -> go k (M.map (action m *** action m) ctx, (v, error "eval.Lam") : map (action m *** action m) lctx) as
eval n ctx (Pi [] e) = eval n ctx e
eval 0 (ctx,lctx) (Pi ((vs,t):ts) e) = go ctx lctx vs
  where
    tv = eval 0 (ctx,lctx) t
    go ctx lctx [] = tv `sarr` eval 0 (ctx,lctx) (Pi ts e)
    go ctx lctx [v] = Spi v tv $ \k m a -> eval k (M.map (action m *** action m) ctx, (a, action (genericReplicate k Ud) tv) : map (action m *** action m) lctx) (Pi ts e)
    go ctx lctx (v:vs) = Spi v tv $ \k m a -> go (M.map (action m *** action m) ctx) ((a, action (genericReplicate k Ud) tv) : map (action m *** action m) lctx) vs
eval 1 (ctx,lctx) e'@(Pi (([],t):ts) e) = Siso 1
    (eval 0 (M.map (action [Ld] *** action [Ld]) ctx, map (action [Ld] *** action [Ld]) lctx) e')
    (eval 0 (M.map (action [Rd] *** action [Rd]) ctx, map (action [Rd] *** action [Rd]) lctx) e')
    (Slam "f" $ \kf mf vf -> Slam "x" $ \kx mx vx -> app kx (action (mx ++ mf) $ coe $ eval 1 (ctx,lctx) $ Pi ts e) $
                             app kx (action mx vf) $ app kx (action (mx ++ mf) $ coe $ inv 0 $ eval 1 (ctx,lctx) t) vx)
    (Slam "f" $ \kf mf vf -> Slam "x" $ \kx mx vx -> app kx (action (mx ++ mf) $ coe $ inv 0 $ eval 1 (ctx,lctx) $ Pi ts e) $
                             app kx (action mx vf) $ app kx (action (mx ++ mf) $ coe $ eval 1 (ctx,lctx) t) vx)
    (error "TODO: eval.Pi.Siso.1") (error "TODO: eval.Pi.Siso.2")
eval n _ (Pi _ _) = error $ "TODO: eval.Pi: " ++ show n
eval n ctx (Sigma [] e) = eval n ctx e
eval 0 (ctx,lctx) (Sigma ((vs,t):ts) e) = go ctx lctx vs
  where
    tv = eval 0 (ctx,lctx) t
    go ctx lctx [] = tv `sarr` eval 0 (ctx,lctx) (Sigma ts e)
    go ctx lctx [v] = Ssigma v tv $ \k m a -> eval k (M.map (action m *** action m) ctx, (a, action (genericReplicate k Ud) tv) : map (action m *** action m) lctx) (Sigma ts e)
    go ctx lctx (v:vs) = Ssigma v tv $ \k m a -> go (M.map (action m *** action m) ctx) ((a, action (genericReplicate k Ud) tv) : map (action m *** action m) lctx) vs
eval n _ (Sigma _ _) = error $ "TODO: eval.Sigma: " ++ show n
eval n ctx (App e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n (ctx,_) (Var v) = fst $ fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval _ _ NoVar = error "eval.NoVar"
eval n (_,ctx) (LVar v) = fst $ ctx `genericIndex` v
eval _ ctx Suc = Slam "n" $ \_ _ -> Ssuc
eval _ ctx Rec = Slam "P" $ \pk pm pv ->
                 Slam "z" $ \zk zm zv ->
                 Slam "s" $ \sk sm sv ->
                 Slam "x" $ \xk xm    ->
        rec xk (action xm $ action sm $ action zm pv)
               (action xm $ action sm             zv)
               (action xm                         sv)
eval n _ (NatConst c) = action (genericReplicate n Ud) (genConst c)
  where
    genConst 0 = Szero
    genConst k = Ssuc $ genConst (k - 1)
eval n ctx (Typed e _) = eval n ctx e
eval 0 _ Nat = Snat
eval n _ Nat = Siso n Snat Snat idf idf idf idf
eval 0 _ (Universe u) = Stype u
eval n _ (Universe u) = Siso n (Stype u) (Stype u) idf idf idf idf
eval 0 ctx (Id t a b) = Sid (eval 0 ctx t) (eval 0 ctx a) (eval 0 ctx b)
eval 1 (ctx,lctx) e@(Id t a b) = Siso 1 (eval 0 (ctxl,lctxl) e) (eval 0 (ctxr,lctxr) e)
    (Slam "p" lr) (Slam "p" rl) (error "TODO: eval.Id.Iso.1") (error "TODO: eval.Id.Iso.2")
  where
    lr k m v = comp k (action m $ inv 0 ap) $
               comp k (pmap k (action (Ud:m) $ coe tp) v)
                      (action m bp)
    rl 0 _ v = comp 0 (pmap 0 (idp 0 $ Slam "p" $ \kp mp vp -> app kp (coe vp) $ action mp a1) $ inv 0 iitp) $
               comp 0 (pmap 0 (coe $ inv 0 tp) $ comp 0 ap $ comp 0 v $ inv 0 bp)
                      (pmap 0 (idp 0 $ Slam "p" $ \kp mp vp -> app kp (coe vp) $ action mp b1) iitp)
    rl k _ _ = error $ "TODO: eval.Id.inv: " ++ show k
    
    ctxl = M.map (action [Ld] *** action [Ld]) ctx
    ctxr = M.map (action [Rd] *** action [Rd]) ctx
    lctxl = map (action [Ld] *** action [Ld]) lctx
    lctxr = map (action [Rd] *** action [Rd]) lctx
    a1 = eval 0 (ctxl,lctxl) a
    b1 = eval 0 (ctxl,lctxl) b
    ap = eval 1 (ctx,lctx) a
    bp = eval 1 (ctx,lctx) b
    tp = eval 1 (ctx,lctx) t
    iitp = invIdp 0 tp
    -- v : Id t2 a2 b2
    -- rl 0 _ v : Id t1 a1 b1
    -- eval 1 ctx t : t1 = t2
    -- eval 1 ctx a : coe (eval 1 ctx t) a1 = a2
    -- eval 1 ctx b : coe (eval 1 ctx t) b1 = b2
    --   a1
    -- < pmap 0 (idp $ \p -> coe p a1) (inv 0 $ invIdp 0 $ eval 1 ctx t) >
    -- = coe (inv (eval 1 ctx t); eval 1 ctx t) a1
    -- = coe (inv (eval 1 ctx t)) (coe (eval 1 ctx t) a1)
    -- < pmap 0 (coe $ inv 0 $ eval 1 ctx t) (eval 1 ctx a) >
    -- = coe (inv (eval 1 ctx t)) a2
    -- < pmap 0 (...) v >
    -- = coe (inv (eval 1 ctx t)) b2
    -- < pmap 0 (...) (inv 0 $ eval 1 ctx b) >
    -- = coe (inv (eval 1 ctx t)) (coe (eval 1 ctx t) b1)
    -- = coe (inv (eval 1 ctx t); eval 1 ctx t) b1
    -- < pmap 0 (idp $ \p -> coe p b1) (invIdp 0 $ eval 1 ctx t) >
    -- = b1
eval n _ (Id _ _ _) = error $ "TODO: eval.Id: " ++ show n

rec :: Integer -> Value -> Value -> Value -> Value -> Value
rec 0 p z s = go
  where
    go Szero = z
    go (Ssuc x) = app 0 (app 0 s x) (go x)
    go t@(Ne [] e) =
        let r l = Rec `App` reify l p (Snat `sarr` Stype maxBound)
                      `App` reify l z (app 0 p Szero)
                      `App` reify l s (Spi "x" Snat $ \k m x -> app k (action m p) x `sarr` app k (action m p) (Ssuc x))
                      `App` e l
        in liftTerm r (app 0 p t)
    go _ = error "rec.0"
-- rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (suc x)) -> (x : Nat) -> P x
-- pmap (idp rec) : (P : P1 = P2) -> (z : Idp (P2 0) (coe (pmap P (idp 0)) z1) z2)
--      -> (s : Idp ((x : Nat) -> P2 x -> P2 (suc x)) (trans (\P -> (x : Nat) -> P x -> P (suc x)) P s1) s2) -> ...
-- pmap (pmap (pmap (pmap (idp rec) P) z) s) x : coe (pmap p x) (rec P1 z1 s1 x1) = rec P2 z2 s2 x2
rec 1 p z s = go
  where
    go Szero = z
    go (Ssuc x) = app 1 (app 1 s x) (go x)
    go (Sidp (Ne [] e)) = go $ Ne [(e,e)] (App Idp . e)
    go x@(Ne [(el,er)] e) =
        let r l = Pmap `App` (Pmap `App` (Pmap `App` (Pmap `App` (Idp `App` Rec)
                `App` reify l p (Sid (Snat `sarr` Stype Omega) (action [Ld] p) (action [Rd] p)))
                `App` reify l z
                    (Sid (app 0 (app 0 (pmap 0 p Szero) $ action [Rd] p) Szero) (action [Ld] z) (action [Rd] z)))
                `App` (let t p2 = Pi [(["x"],Nat)] $ Pi [([],App (Var p2) (Var "x"))] $ App (Var "P2") $ App Suc (Var "x")
                       in reify l s $ eval 0 (M.fromList [ ("P" , (p, Snat `sarr` Stype maxBound))
                                                         , ("s1", (action [Ld] s, error "TODO: rec.1.1"))
                                                         , ("s2", (action [Rd] s, error "TODO: rec.1.2"))
                                                         ], [])
                        $ Id (t "P") (Coe `App` (Pmap `App` Lam ["P2"] (t "P2") `App` Var "P") `App` Var "s1") (Var "s2")))
                `App` e l
        in liftTerm r $ Sid (app 0 (action [Rd] p) $ Ne [] er)
            (app 0 (coe $ pmap 0 p x) $ rec 0 (action [Ld] p) (action [Ld] z) (action [Ld] s) (Ne [] el))
            (rec 0 (action [Rd] p) (action [Rd] z) (action [Rd] s) (Ne [] er))
    go _ = error "rec.1"
rec n _ _ _ = error $ "TODO: rec: " ++ show n

typeOfTerm :: Integer -> Ctx -> Term -> Value
typeOfTerm n ctx (Let defs e) = typeOfTerm n (updateCtx n ctx defs) e
typeOfTerm n ctx (Lam [] e) = typeOfTerm n ctx e
typeOfTerm _ _ (Lam _ _) = error "typeOfTerm.Lam"
typeOfTerm n ctx (Pi [] e) = typeOfTerm n ctx e
typeOfTerm 0 (ctx,lctx) (Pi ((vars,t):vs) e) =
    let r = typeOfTerm 0 (ctx, updateLCtx (genericLength lctx) (eval 0 (ctx,lctx) t) lctx vars) (Pi vs e)
    in case (typeOfTerm 0 (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Pi"
typeOfTerm n ctx (Pi ((vars,t):vs) e) = error $ "TODO: typeOfTerm.Pi: " ++ show n
typeOfTerm n ctx (Sigma [] e) = typeOfTerm n ctx e
typeOfTerm 0 (ctx,lctx) (Sigma ((vars,t):vs) e) =
    let r = typeOfTerm 0 (ctx, updateLCtx (genericLength lctx) (eval 0 (ctx,lctx) t) lctx vars) (Sigma vs e)
    in case (typeOfTerm 0 (ctx,lctx) t, r) of
        (Stype k1, Stype k2) -> Stype (max k1 k2)
        _ -> error "typeOfTerm.Sigma"
typeOfTerm n ctx (Sigma ((vars,t):vs) e) = error $ "TODO: typeOfTerm.Sigma: " ++ show n
typeOfTerm 0 ctx (Pair e1 e2) = typeOfTerm 0 ctx e1 `sprod` typeOfTerm 0 ctx e2
typeOfTerm n ctx (Pair e1 e2) = error $ "TODO: typeOfTerm.Pair: " ++ show n
typeOfTerm _ _ Proj1 = error "typeOfTerm.Proj1"
typeOfTerm 0 ctx (App Proj1 e) = case typeOfTerm 0 ctx e of
    Ssigma _ a _ -> a
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm n ctx (App Proj1 e) = error $ "TODO: typeOfTerm.App.Proj1: " ++ show n
typeOfTerm _ _ Proj2 = error "typeOfTerm.Proj2"
typeOfTerm 0 ctx (App Proj2 e) = case typeOfTerm 0 ctx e of
    Ssigma _ _ b -> b 0 [] $ eval 0 ctx (App Proj1 e)
    _ -> error "typeOfTerm.App.Proj1"
typeOfTerm n ctx (App Proj2 e) = error $ "TODO: typeOfTerm.App.Proj2: " ++ show n
typeOfTerm n ctx (Id t _ _) = typeOfTerm n ctx t
typeOfTerm 0 ctx (App Idp e) =
    let v = eval 0 ctx e
    in Sid (typeOfTerm 0 ctx e) v v
typeOfTerm n ctx (App Idp e) = error $ "TODO: typeOfTerm.App.Idp: " ++ show n
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfTerm 0 ctx (App (App Pmap (App Idp e1)) e2) =
    let e' = eval 0 ctx e1
    in case typeOfTerm 0 ctx e2 of
        Sid t a b -> typeOfLam 0 ctx e1 t (app 0 e' a) (app 0 e' b) (eval 0 ctx e2)
        _ -> error "typeOfTerm.App.App.Pmap.Idp"
typeOfTerm n ctx (App (App Pmap (App Idp e1)) e2) = error $ "TODO: typeOfTerm.App.App.Pmap.Idp: " ++ show n
typeOfTerm 0 ctx (App (App Pmap e1) e2) =
    case (typeOfTerm 0 ctx e1, typeOfTerm 0 ctx e2) of
        (Sid (Spi v _ b) f g, Sid _ x y) ->
            Sid (b 0 [] y) (trans 0 (Slam v b) (eval 0 ctx e2) (app 0 f x)) (app 0 g y)
        _ -> error "typeOfTerm.App.App.Pmap"
typeOfTerm n ctx (App (App Pmap e1) e2) = error $ "TODO: typeOfTerm.App.App.Pmap: " ++ show n
typeOfTerm 0 ctx (App Coe e) = case typeOfTerm 0 ctx e of
    Sid _ x y -> x `sarr` y
    _ -> error "typeOfTerm.App.Coe"
typeOfTerm n ctx (App Coe e) = error $ "TODO: typeOfTerm.App.Coe: " ++ show n
typeOfTerm 0 ctx (App Inv e) = case typeOfTerm 0 ctx e of
    Sid t x y -> Sid t y x
    _ -> error "typeOfTerm.App.Inv"
typeOfTerm n ctx (App Inv e) = error $ "TODO: typeOfTerm.App.Inv: " ++ show n
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeOfTerm 0 ctx (App InvIdp e) = case typeOfTerm 0 ctx e of
    t@(Sid _ _ _) ->
        let e' = eval 0 ctx e
        in Sid (Sid t e' e') (comp 0 (inv 0 e') e') (idp 0 e')
    _ -> error "typeOfTerm.App.InvIdp"
typeOfTerm n ctx (App InvIdp e) = error $ "TODO: typeOfTerm.App.InvIdp: " ++ show n
typeOfTerm 0 ctx (App (App Comp e1) e2) = case (typeOfTerm 0 ctx e1, typeOfTerm 0 ctx e2) of
    (Sid t x _, Sid _ _ z) -> Sid t x z
    _ -> error "typeOfTerm.App.Comp"
typeOfTerm n ctx (App (App Comp e1) e2) = error $ "TODO: typeOfTerm.App.App.Comp: " ++ show n
typeOfTerm 0 ctx (App e1 e2) = case (typeOfTerm 0 ctx e1, typeOfTerm 0 ctx e2) of
    (Spi _ _ b, _) -> b 0 [] $ eval 0 ctx e2
    (Sid (Spi _ _ t) f g, Sid _ a b) -> Sid (t 0 [] $ error "typeOfTerm.App.Id") (app 0 f a) (app 0 g b)
    _ -> error "typeOfTerm.App"
typeOfTerm n ctx (App e1 e2) = error $ "TODO: typeOfTerm.App: " ++ show n
typeOfTerm _ (_,ctx) (LVar v) = snd $ ctx `genericIndex` v
typeOfTerm _ ctx NoVar = error "typeOfTerm.NoVar"
typeOfTerm _ (ctx,_) (Var v) = case M.lookup v ctx of
    Nothing -> error $ "typeOfTerm.Var: " ++ v
    Just (_,t) -> t
typeOfTerm n _ Nat = action (genericReplicate n Ud) $ Stype (Finite 0)
typeOfTerm n _ Suc = action (genericReplicate n Ud) $ Snat `sarr` Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm n _ Rec = action (genericReplicate n Ud) $
    eval 0 (M.empty,[]) $ Pi [(["P"], Pi [([],Nat)] $ Universe Omega)] $
    Pi [([], App (LVar 0) $ NatConst 0)] $ Pi [([], iht)] $ Pi [(["x"],Nat)] $ App (LVar 1) (LVar 0)
  where iht = Pi [(["x"],Nat)] $ Pi [([], App (LVar 1) (LVar 0))] $ App (LVar 1) $ App Suc (LVar 0)
typeOfTerm n ctx (Typed _ t) = eval n ctx t
-- typeOfTerm 0 ctx (Ext f g) = -> Sid (typeOfTerm 0 ctx f) (eval 0 ctx f) (eval 0 ctx g)
typeOfTerm n ctx (Ext f g) = error $ "TODO: typeOfTerm.Ext: " ++ show n
-- typeOfTerm 0 ctx (ExtSigma p q) = Sid (typeOfTerm 0 ctx p) (eval 0 ctx p) (eval 0 ctx q)
typeOfTerm n ctx (ExtSigma f g) = error $ "TODO: typeOfTerm.ExtSigma: " ++ show n
typeOfTerm n _ (NatConst _) = action (genericReplicate n Ud) Snat
typeOfTerm n _ (Universe l) = action (genericReplicate n Ud) $ Stype (succ l)
typeOfTerm _ _ Pmap = error "typeOfTerm.Pmap"
typeOfTerm _ _ Idp = error "typeOfTerm.Idp"
typeOfTerm _ _ Coe = error "typeOfTerm.Coe"
typeOfTerm _ _ Comp = error "typeOfTerm.Comp"
typeOfTerm _ _ Inv = error "typeOfTerm.Inv"
typeOfTerm _ _ InvIdp = error "typeOfTerm.InvIdp"
typeOfTerm n _ Iso = 
    let term = Pi [(["A"],Universe $ pred $ pred maxBound)] $
               Pi [(["B"],Universe $ pred $ pred maxBound)] $
               Pi [(["f"],Pi [([],LVar 1)] $ LVar 0)] $
               Pi [(["g"],Pi [([],LVar 1)] $ LVar 2)] $
               Pi [([],Pi [(["a"],LVar 3)] $ Id (LVar 4) (LVar 1 `App` (LVar 2 `App` LVar 0)) (LVar 0))] $
               Pi [([],Pi [(["b"],LVar 2)] $ Id (LVar 3) (LVar 2 `App` (LVar 1 `App` LVar 0)) (LVar 0))] $
               Id (Universe $ pred $ pred maxBound) (Var "A") (Var "B")
    in action (genericReplicate n Ud) $ eval 0 (M.empty,[]) term

typeOfLam :: Integer -> Ctx -> Term -> Value -> Value -> Value -> Value -> Value
typeOfLam n ctx (Let defs e) t a b p = typeOfLam n (updateCtx n ctx defs) e t a b p
typeOfLam n ctx (Lam [] e) t a b p = typeOfLam n ctx e t a b p
typeOfLam n (ctx,lctx) (Lam (x:xs) e) t a b _ = Sid (typeOfTerm n (ctx, (error "typeOfLam.Var", t) : lctx) (Lam xs e)) a b
typeOfLam n ctx e t a b p = case typeOfTerm n ctx e of
    Spi v _ r -> Sid (r 0 [] b) (trans 0 (Slam v r) p a) b
    _ -> error "typeOfLam.Pi"

updateLCtx :: DBIndex -> Value -> [(Value,Value)] -> [String] -> [(Value,Value)]
updateLCtx _ _ lctx [] = lctx
updateLCtx i tv lctx (_:vs) = updateLCtx (i + 1) tv ((svar i tv, tv) : lctx) vs

updateCtx :: Integer -> Ctx -> [Def] -> Ctx
updateCtx _ ctx [] = ctx
updateCtx n actx@(ctx,lctx) (Def name Nothing expr : ds) =
    updateCtx n (M.insert name (eval n actx expr, typeOfTerm n actx expr) ctx, lctx) ds
updateCtx n actx@(ctx,lctx) (Def name (Just (ty,args)) expr : ds) =
    updateCtx n (M.insert name (eval n actx (Lam args expr), eval n actx ty) ctx, lctx) ds
