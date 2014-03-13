module Value
    ( Value(..), ValueFV
    , D(..), GlobMap
    , svar, sarr, sarrFV, sprod
    , Ctx, CtxT, CtxV
    , ctxTToCtx, ctxToCtxT, ctxToCtxV
    , cmpTypes
    , reify, reifyFV
    , valueFreeVars
    , action, app, idp, pmap
    ) where

import qualified Data.Map as M
import Data.List

import Syntax.Common
import Syntax.Term

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Value
    = Slam String [String] (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi String [String] Value (Value -> Value) | Ssigma String [String] Value (Value -> Value) -- Constructors for Type_k
    | Snat | Sid Value Value Value | Stype Level -- Constructors for Type_k
    | Sidp Value -- Constructor for Id
    | Ne Term
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxT = M.Map String Value
type CtxV = M.Map String Value
type ValueFV = (Value,[String])

svar :: String -> Value
svar x = Ne (Var x)

infixr 5 `sarrFV`
sarrFV :: Value -> ValueFV -> Value
sarrFV a (b,fv) = Spi "_" fv a (const b)

infixr 5 `sarr`
sarr :: Value -> Value -> Value
sarr a b = sarrFV a (b,valueFreeVars b)

sprod :: Value -> ValueFV -> Value
sprod a (b,fv) = Ssigma "_" fv a (const b)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

app :: Integer -> Value -> Value -> Value
app n (Slam _ _ f) a = f n [] a
app n (Ne e) a = Ne $ App e (reify a)
app n _ _ = error "Value.app"

idp :: Value -> Value
idp = action [Ud]

pmap :: Integer -> Value -> Value -> Value
pmap n a = app (n + 1) (idp a)

ctxTToCtx :: CtxT -> Ctx
ctxTToCtx = M.mapWithKey $ \k v -> (svar k, v)

ctxToCtxT :: Ctx -> CtxT
ctxToCtxT = M.map snd

ctxToCtxV :: Ctx -> CtxV
ctxToCtxV = M.map fst

cmpTypes :: Value -> Value -> Maybe Ordering
cmpTypes (Spi x v1 a b) (Spi _ v2 a' b') = case (cmpTypes a' a, cmpTypes (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName x (v1 `union` v2)
cmpTypes (Ssigma x v1 a b) (Ssigma _ v2 a' b') = case (cmpTypes a a', cmpTypes (b $ svar fresh) (b' $ svar fresh)) of
    (Just l, Just r) | l == r -> Just l
    _ -> Nothing
    where fresh = freshName x (v1 `union` v2)
cmpTypes (Sid _ a b) (Sid _ a' b') = if cmpValues a a' && cmpValues b b' then Just EQ else Nothing
cmpTypes Snat Snat = Just EQ
cmpTypes (Stype k) (Stype k') = Just (compare k k')
cmpTypes (Ne t) (Ne t') = if t == t' then Just EQ else Nothing
cmpTypes _ _ = Nothing

cmpValues :: Value -> Value -> Bool
cmpValues e1 e2 = reify e1 == reify e2

valueFreeVars :: Value -> [String]
valueFreeVars (Slam _ fv _) = fv
valueFreeVars Szero = []
valueFreeVars (Ssuc e) = valueFreeVars e
valueFreeVars (Spi _ fv _ _) = fv
valueFreeVars (Ssigma _ fv _ _) = fv
valueFreeVars Snat = []
valueFreeVars (Sid t a b) = valueFreeVars t `union` valueFreeVars a `union` valueFreeVars b
valueFreeVars (Stype _) = []
valueFreeVars (Sidp e) = valueFreeVars e
valueFreeVars (Ne e) = freeVars e

reifyFV :: ValueFV -> Term
reifyFV (Slam x _ f, fv) =
    let x' = freshName x fv
    in Lam [x'] $ reifyFV (f 0 [] (svar x'), x':fv)
reifyFV (Szero,_) = NatConst 0
reifyFV (Ssuc e,fv) = case reifyFV (e,fv) of
    NatConst n -> NatConst (n + 1)
    t -> App Suc t
reifyFV (Spi x _ a b,fv) =
    let x' = freshName x fv
    in Pi [([x'],reifyFV (a,valueFreeVars a))] $ reifyFV (b $ svar x', x':fv)
reifyFV (Ssigma x _ a b,fv) =
    let x' = freshName x fv
    in Sigma [([x'],reifyFV (a,valueFreeVars a))] $ reifyFV (b $ svar x', x':fv)
reifyFV (Sid t a b,_) = Id (reifyFV (t,valueFreeVars t)) (reifyFV (a,valueFreeVars a)) $ reifyFV (b,valueFreeVars b)
reifyFV (Stype u,_) = Universe u
reifyFV (Snat,_) = Nat
reifyFV (Sidp x,fv) = App Idp $ reifyFV (x,fv)
reifyFV (Ne e,_) = e

reify :: Value -> Term
reify v = reifyFV (v, valueFreeVars v)
