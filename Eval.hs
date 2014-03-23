module Eval
    ( eval
    , comp, inv
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
eval _ _ Iso =                                                  Slam "A" []      $ \_  _  va ->
    let fva = valueFreeVars va                               in Slam "B" fva     $ \_  mb vb ->
    let fvb = valueFreeVars vb; fvab    = fva    `union` fvb in Slam "f" fvab    $ \_  mf vf ->
    let fvf = valueFreeVars vf; fvabf   = fvab   `union` fvf in Slam "g" fvabf   $ \_  mg vg ->
    let fvg = valueFreeVars vg; fvabfg  = fvabf  `union` fvg in Slam "p" fvabfg  $ \_  mp vp ->
    let fvp = valueFreeVars vp; fvabfgp = fvabfg `union` fvp in Slam "q" fvabfgp $ \kq mq vq ->
    Siso kq (error "TODO: eval.Iso.1") (error "TODO: eval.Iso.2") (error "TODO: eval.Iso.3")
            (error "TODO: eval.Iso.4") (error "TODO: eval.Iso.5") (error "TODO: eval.Iso.6")
eval _ _ Comp = Slam "p" [] $ \_ _ p -> Slam "q" (valueFreeVars p) $ \k m -> comp k (action m p)
eval _ _ Inv = Slam "p" [] $ \k _ -> inv k
eval _ _ InvIdp = Slam "p" [] $ \k _ -> invIdp k
eval _ _ Idp = Slam "x" [] $ \_ _ -> idp
eval _ _ Coe = Slam "p" [] $ \_ _ -> coe
eval _ _ Pmap = Slam "p" [] $ \_ _ p -> Slam "q" (valueFreeVars p) $ \k _ -> pmap k p
-- ext : ((x : A) -> f x = g x) -> f = g
eval n ctx (Ext f g) = Slam "h" [] $ \_ n h -> Slam "p" (valueFreeVars h) $ \k m p -> case (k,lastD m) of
    (0,Just Ld) -> eval 0 (M.map (action $ n ++ m) ctx) f
    (0,Just Rd) -> eval 0 (M.map (action $ n ++ m) ctx) g
    (0,_) -> error "eval.Ext"
    _ -> comp (k - 1) (app k (action m h) $ action [Ld] p) $ app k (eval k (M.map (action $ n ++ m ++ [Ud]) ctx) g) p
eval n ctx (ExtSigma _ _) = idf
eval n ctx (Pair e1 e2) = Spair (eval n ctx e1) (eval n ctx e2)
eval n ctx Proj1 = Slam "p" [] $ \_ _ -> proj1
eval n ctx Proj2 = Slam "p" [] $ \_ _ -> proj2
eval n ctx (Let [] e) = eval n ctx e
eval n ctx (Let (Def v Nothing d : ds) e) = eval n (M.insert v (eval n ctx d) ctx) (Let ds e)
eval n ctx (Let (Def v (Just (_,args)) d : ds) e) = eval n (M.insert v (eval n ctx $ Lam args d) ctx) (Let ds e)
eval n ctx (Lam args e) = go n ctx args
  where
    fv = freeVars e
    go n ctx []     = eval n ctx e
    go n ctx s@(a:as) = Slam a (fv \\ s) $ \k m v -> go k (M.insert a v $ M.map (action m) ctx) as
eval n ctx (Pi [] e) = eval n ctx e
eval n ctx (Pi ((vars,t):ts) e) = go n ctx vars
  where
    efv  = freeVars (Pi ts e)
    pefv = freeVars t `union` efv
    go 0 ctx []       = eval 0 ctx t `sarrFV` (eval 0 ctx (Pi ts e),efv)
    go 0 ctx [v]      = Spi v (delete v efv)  (eval 0 ctx t) $
        \k m a -> eval k (M.insert v a $ M.map (action m) ctx) (Pi ts e)
    go 0 ctx s@(v:vs) = Spi v (pefv \\ s)     (eval 0 ctx t) $
        \k m a -> go   k (M.insert v a $ M.map (action m) ctx) vs
    go 1 ctx [] = Siso 1 (go 0 (M.map (action [Ld]) ctx) []) (go 0 (M.map (action [Rd]) ctx) [])
        (Slam "f" pefv $ \kf mf vf -> Slam "x" (pefv `union` valueFreeVars vf) $
        \kx mx vx -> app kx (action (mx ++ mf) $ coe $ eval 1 ctx $ Pi ts e) $
                            app kx (action mx vf) $ app kx (action (mx ++ mf) $ coe $ inv 0 $ eval 1 ctx t) vx)
        (Slam "f" pefv $ \kf mf vf -> Slam "x" (pefv `union` valueFreeVars vf) $
        \kx mx vx -> app kx (action (mx ++ mf) $ coe $ inv 0 $ eval 1 ctx $ Pi ts e) $
                            app kx (action mx vf) $ app kx (action (mx ++ mf) $ coe $ eval 1 ctx t) vx)
        (error "TODO: eval.Pi.Siso.1") (error "TODO: eval.Pi.Siso.2")
    go 1 ctx (v:vs) = error $ "TODO: eval.Pi: " ++ show n
    go n _ _ = error $ "TODO: eval.Pi: " ++ show n
eval n ctx (Sigma [] e) = eval n ctx e
eval n ctx (Sigma ((vars,t):ts) e) = go n ctx vars
  where
    efv  = freeVars (Sigma ts e)
    pefv = freeVars t `union` efv
    go 0 ctx []       = eval n ctx t `sarrFV` (eval n ctx (Sigma ts e),efv)
    go 0 ctx [v]      = Ssigma v (delete v efv) (eval n ctx t) $
        \k m a -> eval k (M.insert v a $ M.map (action m) ctx) (Sigma ts e)
    go 0 ctx s@(v:vs) = Ssigma v (pefv \\ s)    (eval n ctx t) $
        \k m a -> go   k (M.insert v a $ M.map (action m) ctx) vs
    go n _ _ = error $ "TODO: eval.Sigma: " ++ show n
eval n ctx (App e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n ctx (Var v) = fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval _ ctx Suc = Slam "n" [] $ \_ _ -> Ssuc
eval _ ctx Rec =                                            Slam "P" []    $ \pk pm pv ->
    let pfv = valueFreeVars pv                           in Slam "z" pfv   $ \zk zm zv ->
    let zfv = valueFreeVars zv; pzfv  = pfv  `union` zfv in Slam "s" pzfv  $ \sk sm sv ->
    let sfv = valueFreeVars sv; pzsfv = pzfv `union` sfv in Slam "x" pzsfv $ \xk xm    ->
        rec xk (action xm $ action sm $ action zm pv, pfv)
               (action xm $ action sm             zv, zfv)
               (action xm                         sv, sfv)
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
eval 1 ctx e@(Id t a b) = Siso 1 (eval 0 (M.map (action [Ld]) ctx) e) (eval 0 (M.map (action [Rd]) ctx) e)
    (Slam "p" (freeVars e) lr) (Slam "p" (freeVars e) rl) (error "TODO: eval.Id.Iso.1") (error "TODO: eval.Id.Iso.2")
  where
    lr k m v = comp k (action m $ inv 0 ap) $
               comp k (pmap k (action (Ud:m) $ coe tp) v)
                      (action m bp)
    rl 0 _ v = comp 0 (pmap 0 (idp $ Slam "p" (freeVars a) $ \kp mp vp -> app kp (coe vp) $ action mp a1) $ inv 0 iitp) $
               comp 0 (pmap 0 (coe $ inv 0 tp) $ comp 0 ap $ comp 0 v $ inv 0 bp)
                      (pmap 0 (idp $ Slam "p" (freeVars b) $ \kp mp vp -> app kp (coe vp) $ action mp b1) iitp)
    rl k _ _ = error $ "TODO: eval.Id.inv: " ++ show k
    
    a1 = eval 0 (M.map (action [Ld]) ctx) a
    b1 = eval 0 (M.map (action [Ld]) ctx) b
    ap = eval 1 ctx a
    bp = eval 1 ctx b
    tp = eval 1 ctx t
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

rec :: Integer -> ValueFV -> ValueFV -> ValueFV -> Value -> Value
rec 0 p z s = go
  where
    go Szero = fst z
    go (Ssuc x) = app 0 (app 0 (fst s) x) (go x)
    go t@(Ne [] e) =
        let r = Rec `App` reifyFV p (Snat `sarr` Stype maxBound)
                    `App` reifyFV z (app 0 (fst p) Szero)
                    `App` reifyFV s (Spi "x" (snd p) Snat $ \k m x ->
                        app k (action m $ fst p) x `sarr` app k (action m $ fst p) (Ssuc x))
                    `App` e
        in liftTerm r (app 0 (fst p) t)
    go _ = error "rec.0"
-- rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (suc x)) -> (x : Nat) -> P x
-- pmap (idp rec) : (P : P1 = P2) -> (z : Idp (P2 0) (coe (pmap P (idp 0)) z1) z2)
--      -> (s : Idp ((x : Nat) -> P2 x -> P2 (suc x)) (trans (\P -> (x : Nat) -> P x -> P (suc x)) P s1) s2) -> ...
-- pmap (pmap (pmap (pmap (idp rec) P) z) s) x : coe (pmap p x) (rec P1 z1 s1 x1) = rec P2 z2 s2 x2
rec 1 (p,pfv) (z,zfv) (s,sfv) = go
  where
    go Szero = z
    go (Ssuc x) = app 1 (app 1 s x) (go x)
    go (Sidp (Ne [] e)) = go $ Ne [(e,e)] (App Idp e)
    go x@(Ne [(el,er)] e) =
        let r = Pmap `App` (Pmap `App` (Pmap `App` (Pmap `App` (Idp `App` Rec)
                `App` reifyFV (p,pfv) (Sid (Snat `sarr` Stype Omega) (action [Ld] p) (action [Rd] p)))
                `App` reifyFV (z,zfv)
                    (Sid (app 0 (app 0 (pmap 0 p Szero) $ action [Rd] p) Szero) (action [Ld] z) (action [Rd] z)))
                `App` (let t = Pi [(["x"],Nat)] $ Pi [([],App (Var "P2") (Var "x"))] $ App (Var "P2") $ App Suc (Var "x")
                      in reifyFV (s,sfv) $ eval 0 (M.fromList [("P",p),("s1",action [Ld] s),("s2",action [Rd] s)])
                        $ Id t (Coe `App` (Pmap `App` Lam ["P2"] t `App` Var "P") `App` Var "s1") (Var "s2")))
                `App` e
        in liftTerm r $ Sid (app 0 (action [Rd] p) $ action [Rd] x)
            (app 0 (coe $ pmap 0 p x) $ rec 0 (action [Ld] p,pfv) (action [Ld] z,zfv) (action [Ld] s,sfv) (Ne [] el))
            (rec 0 (action [Rd] p,pfv) (action [Rd] z,zfv) (action [Rd] s,sfv) (Ne [] er))
    go _ = error "rec.1"
rec n _ _ _ = error $ "TODO: rec: " ++ show n

inv :: Integer -> Value -> Value
inv 0 r@(Sidp _) = r
inv 0 (Siso 1 a b f g p q) = Siso 1 b a g f q p
inv 0 (Siso k a b (Slam xf fvf ef) (Slam xg fvg eg) p q) = Siso k a b
    (Slam xf fvf $ \k m v -> inv 0 $ ef k m v) -- TODO: ???
    (Slam xg fvg $ \k m v -> inv 0 $ eg k m v) -- TODO: ???
    (error "TODO: inv.Siso.1") (error "TODO: inv.Siso.2")
inv 0 (Slam x fv f) = Slam x fv $ \k m v -> inv k $ f k m (inv k v)
inv 0 (Ne ((l,r):t) e) = Ne ((r,l):t) (App Inv e)
inv 0 (Spair _ _) = error "TODO: inv.Spair"
inv _ Szero = Szero
inv _ s@(Ssuc _) = s
inv 1 r@(Sidp (Sidp _)) = r
inv 1 (Siso k _ _ _ _ _ _) = error $ "TODO: inv.Siso: " ++ show (1,k)
inv 1 (Sidp (Ne [(a,b)] e)) = Sidp $ Ne [(b,a)] (Inv `App` e)
inv 1 (Ne [(l,r),(a,b)] e) = Ne [(App Inv l, App Inv r), (b,a)] (Pmap `App` App Idp Inv `App` e)
inv n _ = error $ "TODO: inv: " ++ show n

invIdp :: Integer -> Value -> Value
invIdp 0 x@(Sidp _) = Sidp x
invIdp n (Slam x fv f) = Slam x fv $ \k m v -> error $ "TODO: invIdp.Slam: " ++ show n
    {- ? : comp k (inv k $ f k m $ inv k v) (f k m v) = idp (f k m v)
    invIdp k (f k m v) : comp k (inv k $ f k m v) (f k m v) = idp (f k m v) -}
invIdp 0 (Siso 1 a b f g p q) = Siso 2 b b q q (error "TODO: invIdp.Siso.1") (error "TODO: invIdp.Siso.2")
invIdp 0 (Ne [(l,r)] e) = Ne [(Comp `App` (App Inv e) `App` e, App Idp r), (r,r)] $ App (Var "invIdp") e
invIdp n _ = error $ "TODO: invIdp: " ++ show n

comp :: Integer -> Value -> Value -> Value
comp _ (Slam x fv f) (Slam _ fv' g) = Slam x (fv `union` fv') $ \k m v -> comp k (f k m v) (g k m v)
comp 0 (Sidp _) x = x
comp 0 x (Sidp _) = x
comp 0 (Ne ((l,_):t1) e1) (Ne ((_,r):t2) e2) = Ne ((l,r):maxList t1 t2) $ Comp `App` e1 `App` e2
  where maxList t [] = t
        maxList [] t = t
        maxList (x:xs) (_:ys) = x : maxList xs ys
comp 1 (Sidp (Sidp _)) x = x
comp 1 x (Sidp (Sidp _)) = x
comp 1 (Sidp (Ne [(a,_)] e1)) (Sidp (Ne [(_,b)] e2)) = Sidp $ Ne [(a,b)] $ Comp `App` e1 `App` e2
comp 1 (Sidp (Ne [(a,_)] e1)) (Ne [(l2,r2),(_,b)] e2) =
    Ne [(Comp `App` e1 `App` l2, Comp `App` e1 `App` r2),(a,b)] $ Pmap `App` (App Idp $ Comp `App` e1) `App` e2
comp 1 x (Sidp (Ne l e1)) = comp 1 x (Ne ((e1,e1):l) $ App Idp e1)
comp 1 (Ne [(l1,r1),(a,_)] e1) (Ne [(l2,r2),(_,b)] e2) =
    Ne [(Comp `App` l1 `App` l2, Comp `App` r1 `App` r2),(a,b)] $ Pmap `App` (Pmap `App` App Idp Comp `App` e1) `App` e2
comp n _ _ = error $ "TODO: comp: " ++ show n
