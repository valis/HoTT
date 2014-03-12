module Eval
    ( eval
    , typeOfTerm
    , rawDefsToTerm, rawExprToTerm
    ) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import Syntax.Term
import Syntax.Common
import qualified Syntax.Raw as R
import qualified Parser.AbsGrammar as E
import Value

eval :: Integer -> CtxV -> Term -> Value
eval n ctx Idp = Slam "x" [] $ \_ _ -> idp
eval n ctx (Pmap e) = Slam "p" (freeVars e) $ \k m -> pmap k $ eval k (M.map (action m) ctx) e
eval n ctx (Let [] e) = eval n ctx e
eval n ctx (Let (Def v _ d : ds) e) = eval n (M.insert v (eval n ctx d) ctx) (Let ds e)
eval n ctx (Lam args e) = go n ctx args
  where
    fv = freeVars e
    go n ctx []     = eval n ctx e
    go n ctx (a:as) = Slam a (fv \\ args) $ \k m v -> go k (M.insert a v $ M.map (action m) ctx) as
eval n ctx (Pi [] e) = eval n ctx e
eval 0 ctx (Pi ((vars,t):ts) e) = go ctx vars
  where
    tv   = eval 0 ctx t
    efv  = freeVars (Pi ts e)
    pefv = freeVars t `union` efv
    go ctx []     = eval 0 ctx t `sarrFV` (eval 0 ctx (Pi ts e),efv)
    go ctx [v]    = Spi v  efv tv $ \a -> eval 0 (M.insert v a ctx) (Pi ts e)
    go ctx (v:vs) = Spi v pefv tv $ \a -> go     (M.insert v a ctx) vs
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
    go t@(Ne e) = Ne $ Rec `aApp` reifyFV p `aApp` reifyFV z `aApp` reifyFV s `aApp` e
    go _ = error "rec"
rec _ _ _ _ = error "TODO: rec > 0"
    -- example: pmap (\s -> Rec P z s x) (f : P = P) : P x = P x
    -- example: pmap (\z -> Rec P z s 0) p = p
    -- example: pmap (\x -> Rec P z s x) (p : x1 = x2) : Rec P z s x1 = Rec P z s x2

rawDefsToTerm :: Ctx -> [E.Def] -> [Def]
rawDefsToTerm ctx [] = []
rawDefsToTerm ctx (E.DefType _ t : E.Def (E.PIdent (_,name)) args e : defs) =
    Def name (Just (rawExprToTerm ctx t, map R.unArg args)) (rawExprToTerm ctx e) : rawDefsToTerm ctx defs
rawDefsToTerm ctx (E.Def (E.PIdent (_,name)) [] e : defs) = Def name Nothing (rawExprToTerm ctx e) : rawDefsToTerm ctx defs
rawDefsToTerm _ _ = error "rawDefsToTerm"

exprToVars :: E.Expr -> [String]
exprToVars = reverse . go
  where
    go (E.Var (E.NoArg _)) = ["_"]
    go (E.Var (E.Arg (E.PIdent (_,x)))) = [x]
    go (E.App a (E.Var (E.NoArg _))) = "_" : go a
    go (E.App a (E.Var (E.Arg (E.PIdent (_,x))))) = x : go a
    go _ = error "exprToVars"

rawExprToTerm :: Ctx -> E.Expr -> Term
rawExprToTerm ctx (E.Let defs expr) = Let (rawDefsToTerm ctx defs) (rawExprToTerm ctx expr)
rawExprToTerm ctx (E.Lam _ args expr) = Lam (map R.unBinder args) (rawExprToTerm ctx expr)
rawExprToTerm ctx (E.Pi tvs e) =
    Pi (map (\(E.TypedVar _ vars t) -> (exprToVars vars, rawExprToTerm ctx t)) tvs) (rawExprToTerm ctx e)
rawExprToTerm ctx (E.Sigma tvs e) =
    Sigma (map (\(E.TypedVar _ vars t) -> (exprToVars vars, rawExprToTerm ctx t)) tvs) (rawExprToTerm ctx e)
rawExprToTerm ctx (E.Arr e1 e2) = Pi [([], rawExprToTerm ctx e1)] (rawExprToTerm ctx e2)
rawExprToTerm ctx (E.Prod e1 e2) = Sigma [([], rawExprToTerm ctx e1)] (rawExprToTerm ctx e2)
rawExprToTerm ctx (E.Id e1 e2) =
    let e1' = rawExprToTerm ctx e1
    in Id (reify $ typeOfTerm ctx e1') e1' (rawExprToTerm ctx e2)
rawExprToTerm ctx (E.App e1 e2) = App (rawExprToTerm ctx e1) (rawExprToTerm ctx e2)
rawExprToTerm ctx (E.Pmap _ e) = Pmap (rawExprToTerm ctx e)
rawExprToTerm ctx (E.Var a) = Var (R.unArg a)
rawExprToTerm ctx (E.Nat _) = Nat
rawExprToTerm ctx (E.Suc _) = Suc
rawExprToTerm ctx (E.Rec _) = Rec
rawExprToTerm ctx (E.Idp _) = Idp
rawExprToTerm ctx (E.NatConst (E.PInt (_,x))) = NatConst (read x)
rawExprToTerm ctx (E.Universe (E.U (_,x))) = Universe (parseLevel x)
rawExprToTerm ctx (E.Paren _ e) = rawExprToTerm ctx e

typeOfTerm :: Ctx -> Term -> Value
typeOfTerm = undefined
{-
typeOfTerm ctx (Let defs e) = undefined
typeOfTerm ctx (Lam [] e) = typeOfTerm ctx e
typeOfTerm ctx (Lam ((v,t):vs) e) = undefined -- Spi "x" (evalTerm t) $ \v -> -- Lam vs e
typeOfTerm ctx (Pi [] e) = typeOfTerm ctx e
typeOfTerm ctx (Pi ((vars,t):vs) e) = case (typeOfTerm ctx t, typeOfTerm ctx (Sigma vs e)) of
    (Stype k1, Stype k2) -> Stype (max k1 k2)
    _ -> error "typeOfTerm.Pi"
typeOfTerm ctx (Sigma [] e) = typeOfTerm ctx e
typeOfTerm ctx (Sigma ((vars,t):vs) e) = case (typeOfTerm ctx t, typeOfTerm ctx (Sigma vs e)) of
    (Stype k1, Stype k2) -> Stype (max k1 k2)
    _ -> error "typeOfTerm.Sigma"
typeOfTerm ctx (Id e _) = typeOfTerm ctx $ reify (M.keys ctx) (typeOfTerm ctx e) (Stype maxBound)
typeOfTerm ctx (App e1 e2) = case typeOfTerm ctx e1 of
    Spi _ _ b -> b (eval 0 ctx e2)
    _ -> error "typeOfTerm.App"
typeOfTerm ctx (Var v) = fromMaybe (error "typeOfTerm.Var") (M.lookup v ctx)
typeOfTerm _ Nat = Stype (Finite 0)
typeOfTerm _ Suc = Snat `sarr` Snat
typeOfTerm _ Rec = Spi "P" (Snat `sarr` Stype maxBound) $ \p -> app 0 p Szero `sarr`
    (Spi "x" Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfTerm ctx (Idp e) = let t = typeOfTerm ctx e in Spi "x" t $ \v -> Sid t v v
typeOfTerm ctx (Pmap e a b) =
    let a' = evalTerm a
        b' = evalTerm b
        e' = evalTerm e
        t = typeOfTerm ctx a
    in case typeOfTerm ctx e of
        Spi _ _ r -> Sid t a' b' `sarr` Sid (r $ error "typeOfTerm.Pmap.Pi") (app 0 e' a') (app 0 e' b')
        _ -> error "typeOfTerm.Pmap"
typeOfTerm _ (NatConst _) = Snat
typeOfTerm _ (Universe l) = Stype (succ l)
-}
