module Value
    ( Value(..), ValueFV
    , D(..), GlobMap
    , svar, sarr, sprod
    , Ctx, CtxT
--    , ctxtToCtx, ctxToCtxt
--    , cmpTypes, cmpValues
    , reify
--    , typeOfTerm
    , valueFreeVars
    , action, app, idp, pmap
    ) where

import qualified Data.Map as M
import Data.List

import Syntax.Term

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Value
    = Slam String [String] (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi String [String] Value (Value -> Value) | Ssigma String [String] Value (Value -> Value) -- Constructors for Type_k
    | Snat | Sid Value Value | Stype Level -- Constructors for Type_k
    | Sidp Value -- Constructor for Id
    | Ne Term
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxT = M.Map String Value
type ValueFV = (Value,[String])

svar :: String -> Value
svar x = Ne (Var x)

infixr 5 `sarr`
sarr :: Value -> ValueFV -> Value
sarr a (b,fv) = Spi "_" fv a (const b)

sprod :: Value -> ValueFV -> Value
sprod a (b,fv) = Ssigma "_" fv a (const b)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

app :: Integer -> Value -> Value -> Value
app n (Slam _ _ f) a = f n [] a
app n (Ne e) a = Ne $ App e $ reify (a, valueFreeVars a)
app n _ _ = error "Value.app"

idp :: Value -> Value
idp = action [Ud]

pmap :: Integer -> Value -> Value -> Value
pmap n a = app (n + 1) (idp a)

{-
ctxtToCtx :: CtxT -> Ctx
ctxtToCtx = M.mapWithKey $ \k v -> (svar k, v)

ctxToCtxt :: Ctx -> CtxT
ctxToCtxt = M.map snd

cmpTypes :: [String] -> Value -> Value -> Maybe Ordering
cmpTypes ctx (Spi x a b) (Spi _ a' b') = case (cmpTypes ctx a' a, cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName x ctx
          ctx' = fresh:ctx
cmpTypes ctx (Ssigma x a b) (Ssigma _ a' b') = case (cmpTypes ctx a a', cmpTypes ctx' (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName x ctx
          ctx' = fresh:ctx
cmpTypes ctx (Sid t a b) (Sid t' a' b') = case cmpTypes ctx t t' of
    Nothing -> Nothing
    Just GT -> if cmpValues ctx a a' && cmpValues ctx b b' then Just EQ else Nothing
    _       -> if cmpValues ctx a a' && cmpValues ctx b b' then Just EQ else Nothing
cmpTypes _ Snat Snat = Just EQ
cmpTypes _ (Stype k) (Stype k') = Just (compare k k')
cmpTypes _ (Ne t) (Ne t') = if t == t' then Just EQ else Nothing
cmpTypes _ _ _ = Nothing

cmpValues :: ValueFV -> ValueFV -> Bool
cmpValues e1 e2 = reify e1 == reify e2
-}

valueFreeVars :: Value -> [String]
valueFreeVars (Slam _ fv _) = fv
valueFreeVars Szero = []
valueFreeVars (Ssuc e) = valueFreeVars e
valueFreeVars (Spi _ fv _ _) = fv
valueFreeVars (Ssigma _ fv _ _) = fv
valueFreeVars Snat = []
valueFreeVars (Sid a b) = valueFreeVars a `union` valueFreeVars b
valueFreeVars (Stype _) = []
valueFreeVars (Sidp e) = valueFreeVars e
valueFreeVars (Ne e) = freeVars e

reify :: ValueFV -> Term
reify (Slam x _ f, fv) =
    let x' = freshName x fv
    in Lam [x'] $ reify (f 0 [] (svar x'), x':fv)
reify (Szero,_) = NatConst 0
reify (Ssuc e,fv) = case reify (e,fv) of
    NatConst n -> NatConst (n + 1)
    t -> App Suc t
reify (Spi x _ a b,fv) =
    let x' = freshName x fv
    in Pi [([x'],reify (a,valueFreeVars a))] $ reify (b $ svar x', x':fv)
reify (Ssigma x _ a b,fv) =
    let x' = freshName x fv
    in Sigma [([x'],reify (a,valueFreeVars a))] $ reify (b $ svar x', x':fv)
reify (Sid a b,_) = Id (reify (a,valueFreeVars a)) $ reify (b,valueFreeVars b)
reify (Stype u,_) = Universe u
reify (Snat,_) = Nat
reify (Sidp x,fv) = App Idp $ reify (x,fv)
reify (Ne e,_) = e

{-
typeOfTerm :: CtxT -> Term -> Value
typeOfTerm = undefined
typeOfTerm ctx (Let defs e) = undefined
typeOfTerm ctx (Lam [] e) = typeOfTerm ctx e
typeOfTerm ctx (Lam ((v,t):vs) e) = Spi "x" (evalTerm t) $ \v -> -- Lam vs e
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
    Spi _ _ b -> b (evalTerm e2)
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
