module Eval
    ( eval
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

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
eval _ _ Idp = Slam "x" $ \m -> idp (dom m)
eval _ _ Coe = Slam "p" $ \m -> coe (dom m)
-- pmap : {f g : (a : A) -> B a} -> f = g -> (p : a = a') -> transport B p (f a) = g a'
eval n ctx (Pmap p q) = pmap n (eval n ctx p) (eval n ctx q)
eval n ctx (Pair e1 e2) = Spair (eval n ctx e1) (eval n ctx e2)
eval n ctx Proj1 = Slam "p" $ \_ -> proj1
eval n ctx Proj2 = Slam "p" $ \_ -> proj2
eval n ctx (Let [] e) = eval n ctx e
eval n ctx@(gctx,lctx) (Let (Def v Nothing d : ds) e) = eval n (gctx, eval n ctx d : lctx) (Let ds e)
eval n ctx@(gctx,lctx) (Let (Def v (Just (_,args)) d : ds) e) = eval n (gctx, eval n ctx (Lam 0 args d) : lctx) (Let ds e)
eval n ctx (Lam _ args e) = go n ctx args
  where
    go n ctx []     = eval n ctx e
    go n (ctx,lctx) s@(a:as) = Slam a $ \m v -> go (dom m) (M.map (action m) ctx, v : map (action m) lctx) as
eval n ctx (Pi _ [] e) = eval n ctx e
eval n (ctx,lctx) (Pi n' ((vs,t):ts) e) = go n ctx lctx vs
  where
    tv = eval n (ctx,lctx) t
    go n ctx lctx [] = sarr tv $ eval n (ctx,lctx) (Pi n' ts e)
    go _ ctx lctx [v] = Spi tv $ Slam v $ \m a -> eval (dom m) (M.map (action m) ctx, a : map (action m) lctx) (Pi n' ts e)
    go n ctx lctx (v:vs) = Spi tv $ Slam v $ \m a -> go (dom m) (M.map (action m) ctx) (a : map (action m) lctx) vs
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
eval n ctx (Sigma _ [] e) = eval n ctx e
eval n (ctx,lctx) (Sigma n' ((vs,t):ts) e) = go n ctx lctx vs
  where
    tv = eval n (ctx,lctx) t
    go n ctx lctx [] = sprod tv $ eval n (ctx,lctx) (Sigma n' ts e)
    go _ ctx lctx [v] = Ssigma tv $ Slam v $ \m a -> eval (dom m) (M.map (action m) ctx, a : map (action m) lctx) (Sigma n' ts e)
    go n ctx lctx (v:vs) = Ssigma tv $ Slam v $ \m a -> go (dom m) (M.map (action m) ctx) (a : map (action m) lctx) vs
eval n ctx (App _ e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n (ctx,_) (Var v) = fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval _ _ NoVar = error "eval.NoVar"
eval n (_,ctx) (LVar v) = ctx `genericIndex` v
eval _ ctx Suc = Slam "n" $ \_ -> Ssuc
eval _ ctx Rec = Slam "P" $ \pm pv ->
                 Slam "z" $ \zm zv ->
                 Slam "s" $ \sm sv ->
                 Slam "x" $ \xm    ->
        rec (dom xm) (action xm $ action sm $ action zm pv)
                     (action xm $ action sm             zv)
                     (action xm                         sv)
eval n _ (NatConst c) = genConst c
  where
    genConst 0 = Szero
    genConst k = Ssuc $ genConst (k - 1)
eval n _ Nat = Snat
eval n _ (Universe u) = Stype u
eval n ctx (Id _ t a b) = Sid (eval n ctx t) (eval n ctx a) (eval n ctx b)

infixl 5 `app0`
app0 :: Term -> Term -> Term
app0 = App 0

rec :: Integer -> Value -> Value -> Value -> Value -> Value
rec 0 p z s = go
  where
    go Szero = z
    go (Ssuc x) = app 0 (app 0 s x) (go x)
    go t@(Ne _ e) =
        let r l = Rec `app0` reify l 0 p (sarr Snat $ Stype maxBound)
                      `app0` reify l 0 z (app 0 p Szero)
                      `app0` reify l 0 s (Spi Snat $ Slam "x" $ \m x ->
                            sarr (app (dom m) (action m p) x) $ app (dom m) (action m p) (Ssuc x))
                      `app0` e l
        in reflect 0 r (app 0 p t)
    go _ = error "rec.0"
-- rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (suc x)) -> (x : Nat) -> P x
-- pmap (idp rec) : (P : P1 = P2) -> (z : Idp (P2 0) (coe (pmap P (idp 0)) z1) z2)
--      -> (s : Idp ((x : Nat) -> P2 x -> P2 (suc x)) (trans (\P -> (x : Nat) -> P x -> P (suc x)) P s1) s2) -> ...
-- pmap (pmap (pmap (pmap (idp rec) P) z) s) x : coe (pmap p x) (rec P1 z1 s1 x1) = rec P2 z2 s2 x2
{-
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
-}
rec n _ _ _ = error $ "TODO: rec: " ++ show n
