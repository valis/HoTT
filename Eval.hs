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
    go 0 ctx []       = eval n ctx t `sarrFV` (eval n ctx (Pi ts e),efv)
    go 0 ctx [v]      = Spi v (delete v efv) (eval n ctx t) $
        \k m a -> eval k (M.insert v a $ M.map (action m) ctx) (Pi ts e)
    go 0 ctx s@(v:vs) = Spi v (pefv \\ s)    (eval n ctx t) $
        \k m a -> go   k (M.insert v a $ M.map (action m) ctx) vs
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
eval n _ Nat = Siso n Snat Snat idf idf
eval 0 _ (Universe u) = Stype u
eval n _ (Universe u) = Siso n (Stype u) (Stype u) idf idf
eval 0 ctx (Id t a b) = Sid (eval 0 ctx t) (eval 0 ctx a) (eval 0 ctx b)
eval 1 ctx e@(Id t a b) = Siso 1 (eval 0 (M.map (action [Ld]) ctx) e) (eval 0 (M.map (action [Rd]) ctx) e)
    (Slam "p" (freeVars e) lr) (error "eval.Id.inv")
  where
    lr k _ v = comp k (inv k $ action (genericReplicate k Ud) $ eval 1 ctx a) $
               comp k (pmap k (action (genericReplicate (k + 1) Ud) $ coe $ eval 1 ctx t) v)
               (action (genericReplicate k Ud) $ eval 1 ctx b)
-- v : Id t1 a1 b1
-- r : Id t2 a2 b2
-- eval 1 ctx t : t1 = t2
-- eval 1 ctx a : coe (eval 1 ctx t) a1 = a2
-- eval 1 ctx b : coe (eval 1 ctx t) b1 = b2
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
inv n _ = error $ "TODO: inv: " ++ show n

comp :: Integer -> Value -> Value -> Value
comp _ (Slam x fv f) (Slam _ fv' g) = Slam x (fv `union` fv') $ \k m v -> comp k (f k m v) (g k m v)
comp 0 (Sidp _) x = x
comp 0 x (Sidp _) = x
comp 0 (Ne _ e1) (Ne _ e2) = Ne [] $ Var "comp" `App` e1 `App` e2
comp 1 (Sidp (Sidp _)) x = x
comp 1 x (Sidp (Sidp _)) = x
comp n _ _ = error $ "TODO: comp: " ++ show n
