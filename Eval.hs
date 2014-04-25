module Eval
    ( eval
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import Syntax.Term
import Value
import Cube

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
eval _ _ Idp = Slam "x" $ \m -> idp (domc m)
eval _ _ Coe = Slam "p" $ \_ p -> Slam "x" $ \m -> coe (domc m) (action m p)
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
    go n (gctx,lctx) s@(a:as) = Slam a $ \m v -> go (domc m) (gctx, v : map (action m) lctx) as
eval n ctx (Pi _ [] e) = eval n ctx e
eval n (gctx,lctx) (Pi n' ((vs,t):ts) e) = go n gctx lctx vs $ eval n (gctx,lctx) t
  where
    go n gctx lctx [] tv = sarr tv $ eval n (gctx,lctx) (Pi n' ts e)
    go n gctx lctx [v] tv =
        Spi tv $ Slam v $ \m a -> eval (domc m) (gctx, a : map (action m) lctx) (Pi n' ts e)
    go n gctx lctx (v:vs) tv = Spi tv $
        Slam v $ \m a -> go (domc m) gctx (a : map (action m) lctx) vs (action m tv)
eval n ctx (Sigma _ [] e) = eval n ctx e
eval n (gctx,lctx) (Sigma n' ((vs,t):ts) e) = go n gctx lctx vs $ eval n (gctx,lctx) t
  where
    go n gctx lctx [] tv = sprod tv $ eval n (gctx,lctx) (Sigma n' ts e)
    go n gctx lctx [v] tv =
        Ssigma tv $ Slam v $ \m a -> eval (domc m) (gctx, a : map (action m) lctx) (Sigma n' ts e)
    go n gctx lctx (v:vs) tv = Ssigma tv $
        Slam v $ \m a -> go (domc m) gctx (a : map (action m) lctx) vs (action m tv)
eval n ctx (App _ e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n (ctx,_) (Var v) = action (cubeMapd $ degMap $ genericReplicate n False) $
    fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval _ _ NoVar = error "eval.NoVar"
eval n (_,ctx) (LVar v) = ctx `genericIndex` v
eval _ ctx Suc = Slam "n" $ \_ -> Ssuc
eval _ ctx Rec = Slam "P" $ \pm pv ->
                 Slam "z" $ \zm zv ->
                 Slam "s" $ \sm sv ->
                 Slam "x" $ \xm    ->
        rec (domc xm) (action xm $ action sm $ action zm pv)
                     (action xm $ action sm             zv)
                     (action xm                         sv)
eval n _ (NatConst c) = genConst c
  where
    genConst 0 = Szero
    genConst k = Ssuc $ genConst (k - 1)
eval n _ Nat = Snat
eval n _ (Universe u) = Stype u
eval n ctx (Id _ t a b) = Sid (eval n ctx t) (eval n ctx a) (eval n ctx b)
eval n ctx (Act m e) = action m (eval n ctx e)
eval n ctx Pcon = error $ "TODO: eval.Pcon " ++ show n
eval n ctx (Comp k e1 e2) = comp n k (eval n ctx e1) (eval n ctx e2)

rec :: Integer -> Value -> Value -> Value -> Value -> Value
rec n p z s = go
  where
    go Szero = z
    go (Ssuc x) = app n (app n s x) (go x)
    go t@(Ne _ (Cube c) e) =
        let r l = App n (App n Rec $ reify l n p $ sarr Snat $ Stype maxBound) $
                  App n (reify l n z $ app n p Szero) $
                  App n (reify l n s $ Spi Snat $ Slam "x" $ \m x ->
                            sarr (app (domc m) (action m p) x) $ app (domc m) (action m p) (Ssuc x))
                        (e l)
            face f = rec (domf f) (action (cubeMapf f) p) (action (cubeMapf f) z) (action (cubeMapf f) s) (c f)
        in reflect n (Cube face) r (app n p t)
    go _ = error "rec"
