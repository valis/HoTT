module Eval
    ( eval
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import Syntax.Common
import Syntax.Term
import Value

eval :: Integer -> CtxV -> Term -> Value
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
eval _ _ Comp = Slam "p" $ \_ _ p -> Slam "q" $ \k m -> comp k (action m p)
eval _ _ Inv = Slam "p" $ \k _ -> inv k
eval _ _ InvIdp = Slam "p" $ \k _ -> invIdp k
eval _ _ Idp = Slam "x" $ \k _ -> idp k
eval _ _ Coe = Slam "p" $ \k _ -> coe k
-- pmap : {f g : (a : A) -> B a} -> f = g -> (p : a = a') -> transport B p (f a) = g a'
eval _ _ Pmap = Slam "p" $ \_ _ p -> Slam "q" $ \k _ -> pmap k p
-- ext : ((x : A) -> f x = g x) -> f = g
eval n (ctx,lctx) (Ext f g) = Slam "h" $ \_ n h -> Slam "p" $ \k m p -> case (k,lastD m) of
    (0,Just Ld) -> eval 0 (M.map (action $ n ++ m) ctx, map (action $ n ++ m) lctx) f
    (0,Just Rd) -> eval 0 (M.map (action $ n ++ m) ctx, map (action $ n ++ m) lctx) g
    (0,_) -> error "eval.Ext"
    _ -> comp (k - 1) (app (k - 1) (action m h) $ action [Ld] p)
                      (app k (eval k (M.map (action $ n ++ m ++ [Ud]) ctx, map (action $ n ++ m ++ [Ud]) lctx) g) p)
eval n ctx (ExtSigma _ _) = idf
eval n ctx (Pair e1 e2) = Spair (eval n ctx e1) (eval n ctx e2)
eval n ctx Proj1 = Slam "p" $ \_ _ -> proj1
eval n ctx Proj2 = Slam "p" $ \_ _ -> proj2
eval n ctx (Let [] e) = eval n ctx e
eval n (ctx,lctx) (Let (Def v Nothing d : ds) e) = eval n (M.insert v (eval n (ctx,lctx) d) ctx, lctx) (Let ds e)
eval n (ctx,lctx) (Let (Def v (Just (_,args)) d : ds) e) =
    eval n (M.insert v (eval n (ctx,lctx) $ Lam args d) ctx, lctx) (Let ds e)
eval n ctx (Lam args e) = go n ctx args
  where
    go n ctx []     = eval n ctx e
    go n (ctx,lctx) s@(a:as) = Slam a $ \k m v -> go k (M.map (action m) ctx, v : map (action m) lctx) as
eval n ctx (Pi [] e) = eval n ctx e
eval n (ctx,lctx) (Pi ((vs,t):ts) e) = go ctx lctx vs
  where
    tv = eval n (ctx,lctx) t
    go ctx lctx [] = sarr n tv $ eval n (ctx,lctx) (Pi ts e)
    go ctx lctx [v] = Spi n v tv $ \k m a -> eval k (M.map (action m) ctx, a : map (action m) lctx) (Pi ts e)
    go ctx lctx (v:vs) = Spi n v tv $ \k m a -> go (M.map (action m) ctx) (a : map (action m) lctx) vs
{-
eval 1 (ctx,lctx) e'@(Pi (([],t):ts) e) = Siso1 $ SisoData
    { sisoLeft = eval 0 (M.map (action [Ld]) ctx, map (action [Ld]) lctx) e'
    , sisoRight = eval 0 (M.map (action [Rd]) ctx, map (action [Rd]) lctx) e'
    , sisoLR = Slam "f" $ \kf mf vf -> Slam "x" $ \kx mx vx ->
        app kx (action (mx ++ mf) $ coe $ eval 1 (ctx,lctx) $ Pi ts e)
               (app kx (action mx vf) $ app kx (action (mx ++ mf) $ coe $ inv 0 $ eval 1 (ctx,lctx) t) vx)
    , sisoRL = Slam "f" $ \kf mf vf -> Slam "x" $ \kx mx vx ->
        app kx (action (mx ++ mf) $ coe $ inv 0 $ eval 1 (ctx,lctx) $ Pi ts e)
               (app kx (action mx vf) $ app kx (action (mx ++ mf) $ coe $ eval 1 (ctx,lctx) t) vx)
    , sisoLI = error "TODO: eval.Pi.Siso.LI"
    , sisoRI = error "TODO: eval.Pi.Siso.RI"
    , sisoInv = error "TODO: eval.Pi.Siso.Inv"
    , sisoOver = error "TODO: eval.Pi.Siso.Over"
    }
-}
eval n ctx (Sigma [] e) = eval n ctx e
eval n (ctx,lctx) (Sigma ((vs,t):ts) e) = go ctx lctx vs
  where
    tv = eval n (ctx,lctx) t
    go ctx lctx [] = sprod n tv $ eval n (ctx,lctx) (Sigma ts e)
    go ctx lctx [v] = Ssigma n v tv $ \k m a -> eval k (M.map (action m) ctx, a : map (action m) lctx) (Sigma ts e)
    go ctx lctx (v:vs) = Ssigma n v tv $ \k m a -> go (M.map (action m) ctx) (a : map (action m) lctx) vs
eval n ctx (App e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n (ctx,_) (Var v) = fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval _ _ NoVar = error "eval.NoVar"
eval n (_,ctx) (LVar v) = ctx `genericIndex` v
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
eval n _ Nat = action (genericReplicate n Ud) Snat
eval n _ (Universe u) = action (genericReplicate n Ud) (Stype u)
eval n ctx (Id t a b) = Sid n (eval n ctx t) (eval n ctx a) (eval n ctx b)
{-
eval 1 (ctx,lctx) e@(Id t a b) = Siso1 $ SisoData
    { sisoLeft = eval 0 (ctxl,lctxl) e
    , sisoRight = eval 0 (ctxr,lctxr) e
    , sisoLR = Slam "p" lr
    , sisoRL = Slam "p" rl
    , sisoLI = error "TODO: eval.Id.Iso.LI"
    , sisoRI = error "TODO: eval.Id.Iso.RI"
    , sisoInv = error "TODO: eval.Id.Iso.Inv"
    , sisoOver = error "TODO: eval.Id.Iso.Over"
    }
  where
    lr k m v = comp k (action m $ inv 0 ap) $
               comp k (pmap k (action (Ud:m) $ coe tp) v)
                      (action m bp)
    rl 0 _ v = comp 0 (pmap 0 (idp 0 $ Slam "p" $ \kp mp vp -> app kp (coe vp) $ action mp a1) $ inv 0 iitp) $
               comp 0 (pmap 0 (coe $ inv 0 tp) $ comp 0 ap $ comp 0 v $ inv 0 bp)
                      (pmap 0 (idp 0 $ Slam "p" $ \kp mp vp -> app kp (coe vp) $ action mp b1) iitp)
    rl k _ _ = error $ "TODO: eval.Id.inv: " ++ show k
    
    ctxl = M.map (action [Ld]) ctx
    ctxr = M.map (action [Ld]) ctx
    lctxl = map (action [Ld]) lctx
    lctxr = map (action [Rd]) lctx
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
-}

rec :: Integer -> Value -> Value -> Value -> Value -> Value
rec 0 p z s = go
  where
    go Szero = z
    go (Ssuc x) = app 0 (app 0 s x) (go x)
    go t@(Ne [] e) =
        let r l = Rec `App` reify l p (sarr 0 Snat $ Stype maxBound)
                      `App` reify l z (app 0 p Szero)
                      `App` reify l s (Spi 0 "x" Snat $ \k m x ->
                            sarr 0 (app k (action m p) x) $ app k (action m p) (Ssuc x))
                      `App` e l
        in reflect r (app 0 p t)
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
                `App` reify l p (Sid 0 (sarr 0 Snat $ Stype Omega) (action [Ld] p) (action [Rd] p)))
                `App` reify l z
                    (Sid 0 (app 0 (app 0 (pmap 0 p Szero) $ action [Rd] p) Szero) (action [Ld] z) (action [Rd] z)))
                `App` (let t = Pi [(["x"],Nat)] $ Pi [([],App (Var "P2") (Var "x"))] $ App (Var "P2") $ App Suc (Var "x")
                       in reify l s $ eval 0 (M.fromList [("P",p),("s1",action [Ld] s),("s2",action [Rd] s)],[])
                        $ Id t (Coe `App` (Pmap `App` Lam ["P2"] t `App` Var "P") `App` Var "s1") (Var "s2")))
                `App` e l
        in reflect r $ Sid 0 (app 0 (action [Rd] p) $ Ne [] er)
            (app 0 (coe 0 $ pmap 0 p x) $ rec 0 (action [Ld] p) (action [Ld] z) (action [Ld] s) (Ne [] el))
            (rec 0 (action [Rd] p) (action [Rd] z) (action [Rd] s) (Ne [] er))
    go _ = error "rec.1"
rec n _ _ _ = error $ "TODO: rec: " ++ show n
