module Value
    ( Value(..)
    , svar, gvar, sarr, sprod
    , Ctx, CtxV
    , ctxToCtxV
    , cmpTypes, cmpValues
    , isFreeVar
    , reify, reifyType
    , proj1, proj2, app, coe, pmap, comp
    , idp, action, reflect
    ) where

import qualified Data.Map as M
import Data.List

import Syntax.Common
import Syntax.Term
import Cube

data Value
    = Slam String (CubeMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spair Value Value -- Constructor for Sigma-types
    | Spi Value Value | Ssigma Value Value | Snat | Stype Level -- Constructors for Type_k
    | Sid Value Value Value
    | Ne DegMap (Cube Value) ITerm
type Ctx  = (M.Map String (Value,Value), [(Value,Value)])
type CtxV = (M.Map String Value, [Value])

sarr :: Value -> Value -> Value
sarr a b = Spi a $ Slam "_" $ \m _ -> action m b

sprod :: Value -> Value -> Value
sprod a b = Ssigma a $ Slam "_" $ \m _ -> action m b

ctxToCtxV :: Ctx -> CtxV
ctxToCtxV (ctx,vs) = (M.map fst ctx, map fst vs)

isFreeVar :: DBIndex -> DBIndex -> Value -> Bool
isFreeVar k i (Slam _ f) = isFreeVar (k + 1) (i + 1) (f (idc 0) go)
  where go = Ne (idd 0) (Cube $ \_ -> go) (\_ -> NoVar)
isFreeVar _ _ Szero = False
isFreeVar k i (Ssuc v) = isFreeVar k i v
isFreeVar k i (Spair a b) = isFreeVar k i a || isFreeVar k i b
isFreeVar k i (Spi a b) = isFreeVar k i a || isFreeVar (k + 1) (i + 1) (app 0 b go)
  where go = Ne (idd 0) (Cube $ \_ -> go) (\_ -> NoVar)
isFreeVar k i (Ssigma a b) = isFreeVar k i a || isFreeVar (k + 1) (i + 1) (app 0 b go)
  where go = Ne (idd 0) (Cube $ \_ -> go) (\_ -> NoVar)
isFreeVar _ _ Snat = False
isFreeVar _ _ (Stype _) = False
isFreeVar k i (Sid t a b) = isFreeVar k i t || isFreeVar k i a || isFreeVar k i b
isFreeVar k i (Ne _ _ t) = elem k $ freeLVars (t i)

cmpTypes :: DBIndex -> Integer -> Value -> Value -> Bool
cmpTypes i n (Spi a b) (Spi a' b') =
    cmpTypes i n a' a && cmpTypes (i + 1) n (app n b $ svar i n a) (app n b' $ svar i n a')
cmpTypes i n (Ssigma a b) (Ssigma a' b') =
    cmpTypes i n a a' && cmpTypes (i + 1) n (app n b $ svar i n a) (app n b' $ svar i n a')
cmpTypes i n (Sid t a b) (Sid t' a' b') = cmpTypes i (n + 1) t t' && cmpValues i n a a' t && cmpValues i n b b' t
cmpTypes _ _ Snat Snat = True
cmpTypes _ _ (Stype k) (Stype k') = k <= k'
cmpTypes i _ (Ne d _ e) (Ne d' _ e') = d == d' && e i == e' i
cmpTypes _ _ _ _ = False

cmpValues :: DBIndex -> Integer -> Value -> Value -> Value -> Bool
cmpValues i n e1 e2 t = reify i n e1 t == reify i n e2 t

svar :: DBIndex -> Integer -> Value -> Value
svar i n = reflect n $ \l -> LVar (l - i - 1)

gvar :: String -> Integer -> Value -> Value
gvar v n = reflect n $ \_ -> Var v

proj1 :: Value -> Value
proj1 (Spair a _) = a
proj1 _ = error "proj1"

proj2 :: Value -> Value
proj2 (Spair _ b) = b
proj2 _ = error "proj2"

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) a = f (idc n) a
app _ _ _ = error "Value.app"

coe :: Integer -> Value -> Value -> Value
coe n (Spi a b) _ = error $ "TODO: coe.Spi " ++ show n
coe n (Ssigma a b) _ = error $ "TODO: coe.Ssigma " ++ show n
coe n (Sid t a b) _ = error $ "TODO: coe.Sid " ++ show n
coe _ Snat x = x
coe _ (Stype _) x = x
coe _ (Ne ds _ _) x | isDeg ds 0 = x
coe n (Ne ds fs t) x = Ne ds (Cube $ \m -> coe (domf m) (unCube fs m) $ action (cubeMapf m) x) $
    \i -> App n (App n Coe $ t i) $ reify i n x $ unCube fs $ faceMap (Minus : genericReplicate n Zero)
coe _ _ _ = error "coe"

pmap :: Integer -> Value -> Value -> Value
pmap n = app (n + 1)

idp :: Integer -> Value -> Value
idp n = action $ cubeMapd $ degMap $ genericReplicate n True ++ [False]

comp :: Integer -> Integer -> Value -> Value -> Value
comp n k _ _ = error $ "TODO: comp " ++ show (n,k)

action :: CubeMap -> Value -> Value
action m v | isIdc m = v
action m (Slam x f) = Slam x $ \m' -> f (composec m' m)
action m (Spair e1 e2) = Spair (action m e1) (action m e2)
action _ Szero = Szero
action _ v@(Ssuc _) = v
action m (Ne ds fs t) =
    let m' = composec m (cubeMapd ds)
    in if isDegMap m'
        then Ne (degs m') fs t
        else action (cubeMapd $ degs m') $ unCube fs (faces m')
action m (Spi a b) = Spi (action m a) (action m b)
action m (Ssigma a b) = Ssigma (action m a) (action m b)
action m Snat = Snat
action m (Sid t a b) = Sid (action m t) (action m a) (action m b)
action m v@(Stype _) = v

reflect :: Integer -> ITerm -> Value -> Value
reflect n e (Sid t _ _) = reflect (n + 1) e t
reflect _ e (Spi a (Slam x b)) =
    Slam x $ \m v -> reflect (domc m) (\i -> App (domc m) (e i) $ reify i (domc m) v $ action m a) (b m v)
reflect n e (Ssigma a b) =
    let e1 = reflect n (\i -> App n Proj1 (e i)) a
    in Spair e1 $ reflect n (\i -> App n Proj2 (e i)) (app n b e1)
reflect n e _ = go n e
  where
    go k e = Ne (idd k) (Cube $ \m -> go (domf m) $ Act (cubeMapf m) . e) e

reify :: DBIndex -> Integer -> Value -> Value -> Term
reify i n v (Sid t _ _) = reify i (n + 1) v t
reify i n (Slam x f) (Spi a b) =
    let v = svar i n a
    in Lam n [x] $ reify (i + 1) n (f (idc n) v) (app n b v)
reify _ _ (Slam _ _) _ = error "reify.Slam"
reify i n (Spair e1 e2) (Ssigma a b) = Pair (reify i n e1 a) (reify i n e2 $ app n b e1)
reify _ _ (Spair _ _) _ = error "reify.Spair"
reify _ n Szero Snat = iterate (App 0 Idp) (NatConst 0) `genericIndex` n
reify _ _ Szero _ = error "reify.Szero"
reify i n (Ssuc e) Snat = iidp n $ case reify i n e Snat of
    NatConst k -> NatConst (k + 1)
    t -> App 0 Suc t
  where iidp k x = iterate (App 0 Idp) x `genericIndex` k
reify _ _ (Ssuc _) _ = error "reify.Ssuc"
reify i n (Spi a (Slam x b)) u@(Stype _) =
    Pi n [([x],reify i n a u)] $ reify (i + 1) n (b (idc n) $ svar i n a) u
reify _ _ (Spi _ _) _ = error "reify.Spi"
reify i n (Ssigma a (Slam x b)) u@(Stype _) =
    Sigma n [([x],reify i n a u)] $ reify (i + 1) n (b (idc n) $ svar i n a) u
reify _ _ (Ssigma _ _) _ = error "reify.Ssigma"
reify i n (Sid t a b) u@(Stype _) = Id n (reify i (n + 1) t u) (reify i n a t) (reify i n b t)
reify _ _ (Sid _ _ _) _ = error "reify.Sid"
reify _ n (Stype u) (Stype _) = iterate (App 0 Idp) (Universe u) `genericIndex` n
reify _ _ (Stype _) _ = error "reify.Stype"
reify _ n Snat (Stype _) = iterate (App 0 Idp) Nat `genericIndex` n
reify _ _ Snat _ = error "reify.Snat"
reify i _ (Ne d _ e) _ | isIdd d = e i
reify i _ (Ne d _ e) _ = Act (cubeMapd d) (e i)

reifyType :: DBIndex -> Integer -> Value -> Term
reifyType i n t = reify i n t (Stype maxBound)
