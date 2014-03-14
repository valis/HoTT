module Eval
    ( eval
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import Syntax.Term
import Value

eval :: Integer -> CtxV -> Term -> Value
eval n ctx Idp = Slam "x" [] $ \_ _ -> idp
eval n ctx (Let [] e) = eval n ctx e
eval n ctx (Let (Def v Nothing d : ds) e) = eval n (M.insert v (eval n ctx d) ctx) (Let ds e)
eval n ctx (Let (Def v (Just (_,args)) d : ds) e) = eval n (M.insert v (eval n ctx $ Lam args d) ctx) (Let ds e)
eval n ctx (Lam args e) = go n ctx args
  where
    fv = freeVars e
    go n ctx []     = eval n ctx e
    go n ctx s@(a:as) = Slam a (fv \\ s) $ \k m v -> go k (M.insert a v $ M.map (action m) ctx) as
eval n ctx (Pi [] e) = eval n ctx e
eval 0 ctx (Pi ((vars,t):ts) e) = go ctx vars
  where
    tv   = eval 0 ctx t
    efv  = freeVars (Pi ts e)
    pefv = freeVars t `union` efv
    go ctx []       = eval 0 ctx t `sarrFV` (eval 0 ctx (Pi ts e),efv)
    go ctx [v]      = Spi v (delete v efv) tv $ \a -> eval 0 (M.insert v a ctx) (Pi ts e)
    go ctx s@(v:vs) = Spi v (pefv \\ s)    tv $ \a -> go     (M.insert v a ctx) vs
eval n ctx (Sigma [] e) = eval n ctx e
eval 0 ctx (Sigma ((v:vars,t):ts) e) = go ctx vars
  where
    tv = eval 0 ctx t
    efv = freeVars (Sigma ts e)
    pefv = freeVars t `union` efv
    go ctx [] = eval 0 ctx t `sprod` (eval 0 ctx (Sigma ts e),efv)
    go ctx [v]    = Ssigma v  efv tv $ \a -> eval 0 (M.insert v a ctx) (Sigma ts e)
    go ctx (v:vs) = Ssigma v pefv tv $ \a -> go     (M.insert v a ctx) vs
eval 0 ctx (Id t e1 e2) = Sid (eval 0 ctx t) (eval 0 ctx e1) (eval 0 ctx e2)
eval n ctx (App e1 e2) = app n (eval n ctx e1) (eval n ctx e2)
eval n ctx (Var v) = fromMaybe (error $ "eval: Unknown identifier " ++ v) (M.lookup v ctx)
eval 0 ctx Nat = Snat
eval _ ctx Suc = Slam "n" [] $ \k _ v -> action (genericReplicate k Ud) $ Ssuc $ action (genericReplicate k Ld) v
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

eval _ _ Nat = error "TODO: eval.Nat > 0"
eval _ _ (Universe _) = error "TODO: eval.U > 0"
eval _ _ (Id _ _ _) = error "TODO: eval.Id > 0"
eval _ _ (Pi _ _) = error "TODO: eval.Pi > 0"
eval _ _ (Sigma _ _) = error "TODO: eval.Sigma > 0"

infixl 5 `aApp`
aApp = App

rec :: Integer -> ValueFV -> ValueFV -> ValueFV -> Value -> Value
rec 0 p z s = go
  where
    go Szero = fst z
    go (Ssuc x) = app 0 (app 0 (fst s) x) (go x)
    go t@(Ne [] e) = Ne [] $ Rec `aApp` reifyFV p `aApp` reifyFV z `aApp` reifyFV s `aApp` e
    go _ = error "rec"
rec _ _ _ _ = error "TODO: rec > 0"
    -- example: pmap (\s -> Rec P z s x) (f : P = P) : P x = P x
    -- example: pmap (\z -> Rec P z s 0) p = p
    -- example: pmap (\x -> Rec P z s x) (p : x1 = x2) : Rec P z s x1 = Rec P z s x2

action :: GlobMap -> Value -> Value
action [] v = v
action m (Slam x fv f) = Slam x fv (\k n -> f k (n ++ m))
action (Ud:m) (Spi x fv a b) = error "TODO: action.Spi"
action (Ud:m) (Ssigma x fv a b) = error "TODO: action.Ssigma"
action (Ud:m) Snat = error "TODO: action.Snat"
action (Ud:m) (Sid t a b) = error "TODO: action.Sid"
action (Ud:m) (Stype _) = error "TODO: action.Stype"
action (Ld:m) (Sidp x) = action m x
action (Rd:m) (Sidp x) = action m x
action (Ld:m) (Ne ((l,_):t) _) = action m (Ne t l)
action (Ld:m) (Ne [] _) = error "action.Ld.Ne"
action (Rd:m) (Ne ((_,r):t) _) = action m (Ne t r)
action (Rd:m) (Ne [] _) = error "action.Rd.Ne"
action (Ud:m) (Ne t e) = action m $ Ne ((e,e):t) (App Idp e)
action (Ud:m) v = action m (Sidp v)

action _ Szero = error "action.Szero"
action _ (Ssuc _) = error "action.Ssuc"
action _ (Spi _ _ _ _) = error "action.Spi"
action _ (Ssigma _ _ _ _) = error "action.Ssigma"
action _ Snat = error "action.Snat"
action _ (Sid _ _ _) = error "action.Sid"
action _ (Stype _) = error "action.Stype"

idp :: Value -> Value
idp = action [Ud]
