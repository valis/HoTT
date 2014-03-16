module Value
    ( Value(..), ValueFV
    , D(..), GlobMap
    , svar, sarr, sarrFV, sprod
    , Ctx, CtxV
    , ctxToCtxV
    , cmpTypes
    , reify, reifyFV
    , valueFreeVars
    , app, liftTerm
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
    | Ne [(Term,Term)] Term
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxV = M.Map String Value
type ValueFV = (Value,[String])

infixr 5 `sarrFV`
sarrFV :: Value -> ValueFV -> Value
sarrFV a (b,fv) = Spi "_" fv a (const b)

infixr 5 `sarr`
sarr :: Value -> Value -> Value
sarr a b = sarrFV a (b,valueFreeVars b)

sprod :: Value -> ValueFV -> Value
sprod a (b,fv) = Ssigma "_" fv a (const b)

ctxToCtxV :: Ctx -> CtxV
ctxToCtxV = M.map fst

cmpTypes :: Value -> Value -> Bool
cmpTypes (Spi x v1 a b) (Spi _ v2 a' b') = cmpTypes a' a && cmpTypes (b $ svar fresh a) (b' $ svar fresh a')
    where fresh = freshName x (v1 `union` v2)
cmpTypes (Ssigma x v1 a b) (Ssigma _ v2 a' b') = cmpTypes a a' && cmpTypes (b $ svar fresh a) (b' $ svar fresh a')
    where fresh = freshName x (v1 `union` v2)
cmpTypes (Sid t a b) (Sid t' a' b') = cmpTypes t t' && cmpValues a a' t && cmpValues b b' t
cmpTypes Snat Snat = True
cmpTypes (Stype k) (Stype k') = k <= k'
cmpTypes (Ne l t) (Ne l' t') = t == t' && l == l'
cmpTypes _ _ = False

cmpValues :: Value -> Value -> Value -> Bool
cmpValues e1 e2 t = reify e1 t == reify e2 t

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
valueFreeVars (Ne l e) = freeVars e `union` concatMap (\(x,y) -> freeVars x `union` freeVars y) l

svar :: String -> Value -> Value
svar x = liftTerm (Var x)

app :: Integer -> Value -> Value -> Value
app n (Slam _ _ f) a = f n [] a
app _ _ _ = error "Value.app"

action :: [D] -> Term -> Term
action [] e = e
action (Ud:a) e = action a $ App Pmap (App Idp e)
action (_:a) (App Pmap (App Idp e)) = action a e
action _ _ = error "Value.action"

-- TODO: remove this
sid :: Value -> Value
sid a = Sid a (error "sid.left") (error "sid.right")

liftTerm :: Term -> Value -> Value
liftTerm e (Spi x _ a b) = Slam x (freeVars e) $ \k m v ->
    liftTerm (App (action m e) $ reify v a) (b v)
liftTerm e (Sid (Spi x _ a b) f g) = Slam x (freeVars e) $ \k m v ->
    liftTerm (App (action m $ App Pmap e) (reify v $ sid a)) $ sid (b v)
liftTerm e _ = Ne [] e

reifyFV :: ValueFV -> Value -> Term
reifyFV (Slam x _ f, fv) (Spi _ _ a b) =
    let x' = freshName x fv
        v = svar x' a
    in Lam [x'] $ reifyFV (f 0 [] v, x':fv) (b v)
reifyFV (Slam x _ h, fv) (Sid t@(Spi _ _ a b) f g) =
    let x' = freshName x fv
        v = svar x' (sid a)
    in App (Ext (reify f t) (reify g t)) $ Lam [x'] $ reifyFV (h 0 [] v, x':fv) (b v)
reifyFV (Slam _ _ _, _) _ = error "reify.Slam"
reifyFV (Szero,_) Snat = NatConst 0
reifyFV (Szero,_) _ = error "reify.Szero"
reifyFV (Ssuc e,fv) Snat = case reifyFV (e,fv) Snat of
    NatConst n -> NatConst (n + 1)
    t -> App Suc t
reifyFV (Ssuc _,_) _ = error "reify.Ssuc"
reifyFV (Spi x _ a b,fv) u@(Stype _) =
    let x' = freshName x fv
    in Pi [([x'],reifyFV (a,valueFreeVars a) u)] $ reifyFV (b $ svar x' a, x':fv) u
reifyFV (Spi _ _ _ _, _) _ = error "reify.Spi"
reifyFV (Ssigma x _ a b,fv) u@(Stype _) =
    let x' = freshName x fv
    in Sigma [([x'],reifyFV (a,valueFreeVars a) u)] $ reifyFV (b $ svar x' a, x':fv) u
reifyFV (Ssigma _ _ _ _, _) _ = error "reify.Ssigma"
reifyFV (Sid t a b,_) u@(Stype _) =
    Id (reifyFV (t,valueFreeVars t) u) (reifyFV (a,valueFreeVars a) t) $ reifyFV (b,valueFreeVars b) t
reifyFV (Sid _ _ _, _) _ = error "reify.Sid"
reifyFV (Stype u,_) (Stype _) = Universe u
reifyFV (Stype _, _) _ = error "reify.Stype"
reifyFV (Snat,_) (Stype _) = Nat
reifyFV (Snat, _) _ = error "reify.Snat"
reifyFV (Sidp x,fv) (Sid t _ _) = App Idp $ reifyFV (x,fv) t
reifyFV (Sidp _,_) _ = error "reify.Sidp"
reifyFV (Ne _ e,_) _ = e

reify :: Value -> Value -> Term
reify v = reifyFV (v, valueFreeVars v)
