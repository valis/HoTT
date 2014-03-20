module Eval
    ( eval
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import Syntax.Term
import Value

eval :: Integer -> CtxV -> Term -> Value
eval _ _ Idp = Slam "x" [] $ \_ _ -> idp
eval _ _ Coe = Slam "p" [] $ \k _ -> coe k
eval _ _ Pmap = Slam "p" [] $ \_ _ p -> Slam "q" (valueFreeVars p) $ \k _ -> pmap k p
-- ext : ((x : A) -> f x = g x) -> f = g
eval n ctx (Ext f g) = Slam "h" [] $ \_ n h -> Slam "p" (valueFreeVars h) $ \k m p -> case (k,reduceD m) of
    (0,m'@(Ld:_)) -> eval 0 (M.map (action $ n ++ m') ctx) f
    (0,m'@(Rd:_)) -> eval 0 (M.map (action $ n ++ m') ctx) g
    (0,_) -> error "eval.Ext"
    _ -> comp (k - 1) (app k (action m h) $ action [Ld] p) $ app k (eval k (M.map (action $ n ++ m ++ [Ud]) ctx) g) p
eval n ctx (ExtSigma _ _) = Slam "t" [] $ \_ _ -> id
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
eval 0 ctx (Id t e1 e2) = Sid (eval 0 ctx t) (eval 0 ctx e1) (eval 0 ctx e2)
eval n ctx (App e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n ctx (Var v) = fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval 0 ctx Nat = Snat
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
eval 0 ctx (Universe u) = Stype u
eval n ctx (Typed e _) = eval n ctx e

eval _ _ Nat = error "TODO: eval.Nat > 0"
eval _ _ (Universe _) = error "TODO: eval.U > 0"
eval _ _ (Id _ _ _) = error "TODO: eval.Id > 0"

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
    go _ = error "rec"
rec _ _ _ _ = error "TODO: rec > 0"
    -- example: pmap (\s -> Rec P z s x) (f : P = P) : P x = P x
    -- example: pmap (\z -> Rec P z s 0) p = p
    -- example: pmap (\x -> Rec P z s x) (p : x1 = x2) : Rec P z s x1 = Rec P z s x2

comp :: Integer -> Value -> Value -> Value
comp _ (Slam x fv f) (Slam _ fv' g) = Slam x (fv `union` fv') $ \k m v -> comp k (f k m v) (g k m v)
comp 0 (Sidp _) x = x
comp 0 x (Sidp _) = x
comp 0 (Ne _ e1) (Ne _ e2) = Ne [] $ Var "comp" `App` e1 `App` e2
comp 1 (Sidp (Sidp _)) x = x
comp 1 x (Sidp (Sidp _)) = x
comp n _ _ = error $ "TODO: comp " ++ show n
