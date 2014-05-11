module Value
    ( Value(..)
    , svar, sarr, sprod
    , Ctx, CtxV
    , ctxToCtxV
    , cmpTypes, cmpValues
    , isFreeVar
    , reify, reifyType
    , proj1, proj2, app, pcoe, pmap, compl, compr, pcomp, inv, pinv
    , idp, pidp, action, reflect, reflect0
    , ppcon, fibr, pfibr
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
    | Spath { unPath :: Value } -- Constructor for Id-types
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
isFreeVar k i (Spath t) = isFreeVar k i t

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
svar i n = go n $ \l -> LVar (l - i - 1)
  where
    go n e a = reflect n (Cube $ \f -> go (domf f) (\l -> Act (cubeMapf f) (e l)) $ action (cubeMapf f) a) e a

proj1 :: Value -> Value
proj1 (Spair a _) = a
proj1 _ = error "proj1"

proj2 :: Value -> Value
proj2 (Spair _ b) = b
proj2 _ = error "proj2"

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) a = f (idc n) a
app _ _ _ = error "Value.app"

fibr :: Bool -> Integer -> Value -> Value -> Value
fibr d n (Spi a b) (Slam v g) = Slam v $ \m x -> if isDegMap m
    then error "TODO: fibr.Slam"
    else case lastFace (faces m) of
            (f, Zero) -> case fibr d (domf f + 1) (action (cubeMapf $ faces m) $ Spi a b) (action (cubeMapf f) $ Slam v g) of
                Slam _ g' -> g' (cubeMapd $ degs m) x
                _ -> error "fibr"
            (f, s) | s == Minus && d || s == Plus && not d -> g (cubeMapc (degs m) f) x
            (f, s) -> case coe d n (Spi a b) (Slam v g) of
                Slam _ g' -> g' (cubeMapc (degs m) f) x
                _ -> error "fibr"
fibr d n (Ssigma a b) (Spair x y) =
    let x' = fibr d n a x
    in Spair x' $ fibr d n (app (n + 1) b x') y
fibr d n (Sid t a b) (Spath x) = Spath $ compr (n + 1) (n + 1) (compl (n + 1) (n + 1) (inv (n + 1) (n + 1) $ pcon n a) (idp (n + 1) x)) (pcon n b)
fibr _ n Snat x = idp n x
fibr _ n (Stype _) x = idp n x
fibr d n (Ne _ fs t) x = Ne (idd $ n + 1) (Cube $ \f -> fibr d (domf f) (unCube fs $ liftf f) $ action (cubeMapf f) x) $
    \i -> Fibr d n (t i) (reify i n x $ unCube fs $ faceMap (genericReplicate (n - 1) Zero ++ [Minus]))
fibr _ _ _ _ = error "fibr"

coe :: Bool -> Integer -> Value -> Value -> Value
coe d n (Spi a b) (Slam v f) = Slam v $ \m x ->
    let a' = action m a
        b' = action (liftc m) b
        x' = coe (not d) (domc m) a' x
    in coe d (domc m) (app (domc m + 1) b' $ fibr (not d) (domc m) a' x) (f m x')
coe d n (Ssigma a b) (Spair x y) = Spair (coe d n a x) $ coe d n (app (n + 1) b $ fibr d n a x) y
coe d n (Sid _ a b) (Spath x) = Spath $ compr n n (compl n n (inv n n a) x) b
coe _ _ Snat x = x
coe _ _ (Stype _) x = x
coe _ _ (Ne ds _ _) x | isDeg ds (domd ds - 1) = x
coe d n (Ne _ fs t) x = Ne (idd n) (Cube $ \f -> coe d (domf f) (unCube fs $ liftf f) $ action (cubeMapf f) x) $
    \i -> App n (App n Coe $ if d then t i else Inv n (t i))
                (reify i n x $ unCube fs $ faceMap (genericReplicate (n - 1) Zero ++ [Minus]))
coe _ _ _ _ = error "coe"

pfibr :: Bool -> Integer -> Value -> Value -> Value
pfibr d n (Spath p) x = Spath (fibr d n p x)
pfibr _ _ _ _ = error "pfibr"

pcoe :: Integer -> Value -> Value -> Value
pcoe n = coe True n . unPath

pmap :: Integer -> Value -> Value -> Value
pmap n (Spath f) (Spath a) = Spath $ app (n + 1) f a
pmap _ _ _ = error "pmap"

idp :: Integer -> Value -> Value
idp n x = action (cubeMapd $ degMap $ genericReplicate n True ++ [False]) x

pidp :: Integer -> Value -> Value
pidp n x = Spath (idp n x)

pinv :: Integer -> Integer -> Value -> Value
pinv n k (Spath p) = Spath (inv n k p)
pinv _ _ _ = error "pinv"

inv :: Integer -> Integer -> Value -> Value
inv n k (Slam v g) = Slam v $ \m x -> if isDegMap m
    then inv (domc m) k $ g m (inv (domc m) k x)
    else case getFace (faces m) k of
        (f1, Zero, _) ->
            let g' = action (cubeMapf $ faces m) (Slam v g)
            in action (cubeMapd $ degs m) $ inv (domf $ faces m) (domf $ faceMap f1) g'
        (f1, Minus, f2) -> g (cubeMapc (degs m) (faceMap $ f1 ++ [Plus] ++ f2)) x
        (f1, Plus, f2) -> g (cubeMapc (degs m) (faceMap $ f1 ++ [Minus] ++ f2)) x
inv n k (Spair a b) = Spair (inv n k a) (inv n k b)
inv _ _ Szero = Szero
inv _ _ x@(Ssuc _) = x
inv n k (Spi a b) = Spi (inv n k a) (inv n k b)
inv n k (Ssigma a b) = Ssigma (inv n k a) (inv n k b)
inv _ _ Snat = Snat
inv _ _ x@(Stype _) = x
inv n k (Sid t a b) = Sid (inv (n + 1) (k + 1) t) (inv n k a) (inv n k b)
inv n k x@(Ne d c e)
    | isDeg d k = x
    | otherwise =
        let face f = case getFace f k of
                        (f1, Zero, _) -> inv (domf f) (domf $ faceMap f1) (unCube c f)
                        (f1, Minus, f2) -> unCube c $ faceMap $ f1 ++ [Plus] ++ f2
                        (f1, Plus, f2) -> unCube c $ faceMap $ f1 ++ [Minus] ++ f2
        in Ne d (Cube face) $ \i -> Inv k (e i)
inv n k (Spath p) = Spath $ inv (n + 1) k p

pcomp :: Integer -> Integer -> Value -> Value -> Value
pcomp n k (Spath p) (Spath q) = Spath (compl n k p q)
pcomp _ _ _ _ = error "pcomp"

compl :: Integer -> Integer -> Value -> Value -> Value
compl n k (Slam v g) (Slam v' g') = Slam v $ \m x -> if isDegMap m
    then let m' = cubeMapc (degMap $ gen (domc m) k True False) (faceMap $ gen (domc m) k Zero Minus)
         in compl (domc m) k (g m $ action m' x) (g' m x)
    else case getFace (faces m) k of
        (f1, Zero, _) ->
            let g1 = action (cubeMapf $ faces m) (Slam v g)
                g1' = action (cubeMapf $ faces m) (Slam v' g')
            in action (cubeMapd $ degs m) $ compl (domf $ faces m) (domf $ faceMap f1) g1 g1'
        (_, Minus, _) -> g m x
        (_, Plus, _) -> g' m x
  where
    gen :: Integer -> Integer -> a -> a -> [a]
    gen n k x y = genericReplicate k x ++ [y] ++ genericReplicate (n - k - 1) x
compl _ _ Szero x = x
compl _ _ x Szero = x
compl _ _ (Ssuc _) x = x
compl _ _ x (Ssuc _) = x
compl n k (Spair a b) (Spair a' b') = Spair (compl n k a a') (compl n k b b')
compl n k (Spi a b) (Spi a' b') = Spi (compl n k a a') (compl n k b b')
compl n k (Ssigma a b) (Ssigma a' b') = Ssigma (compl n k a a') (compl n k b b')
compl _ _ Snat Snat = Snat
compl _ _ x@(Stype _) (Stype _) = x
compl n k (Sid a b c) (Sid a' b' c') = Sid (compl (n + 1) (k + 1) a a') (compl n k b b') (compl n k c c')
compl n k (Ne d _ _) x@(Ne _ _ _) | isDeg d k = x
compl n k (Ne d c e) (Ne d' c' e') =
    let (cd,rd,rd',k') = commonDeg d d' k
        face f = case getFace f k' of
            (f1, Zero, _) -> compl (domf f) (domf $ faceMap f1) (unCube c f) (unCube c' f)
            (_, Minus, _) -> unCube c f
            (_, Plus, _) -> unCube c' f
    in Ne cd (Cube face) $ \i -> Comp k' (Act (cubeMapd rd) $ e i) (Act (cubeMapd rd') $ e' i)
compl n k (Spath p) (Spath p') = Spath $ compl (n + 1) k p p'
compl _ _ _ _ = error "compl"

compr :: Integer -> Integer -> Value -> Value -> Value
compr n k (Slam v g) (Slam v' g') = Slam v $ \m x -> if isDegMap m
    then let m' = cubeMapc (degMap $ gen (domc m) k True False) (faceMap $ gen (domc m) k Zero Plus)
         in compr (domc m) k (g m x) (g' m $ action m' x)
    else case getFace (faces m) k of
        (f1, Zero, _) ->
            let g1 = action (cubeMapf $ faces m) (Slam v g)
                g1' = action (cubeMapf $ faces m) (Slam v' g')
            in action (cubeMapd $ degs m) $ compr (domf $ faces m) (domf $ faceMap f1) g1 g1'
        (_, Minus, _) -> g m x
        (_, Plus, _) -> g' m x
  where
    gen :: Integer -> Integer -> a -> a -> [a]
    gen n k x y = genericReplicate k x ++ [y] ++ genericReplicate (n - k - 1) x
compr _ _ Szero x = x
compr _ _ x Szero = x
compr _ _ (Ssuc _) x = x
compr _ _ x (Ssuc _) = x
compr n k (Spair a b) (Spair a' b') = Spair (compr n k a a') (compr n k b b')
compr n k (Spi a b) (Spi a' b') = Spi (compr n k a a') (compr n k b b')
compr n k (Ssigma a b) (Ssigma a' b') = Ssigma (compr n k a a') (compr n k b b')
compr _ _ Snat Snat = Snat
compr _ _ x@(Stype _) (Stype _) = x
compr n k (Sid a b c) (Sid a' b' c') = Sid (compr (n + 1) (k + 1) a a') (compr n k b b') (compr n k c c')
compr n k x@(Ne _ _ _) (Ne d _ _) | isDeg d k = x
compr n k (Ne d c e) (Ne d' c' e') =
    let (cd,rd,rd',k') = commonDeg d d' k
        face f = case getFace f k' of
            (f1, Zero, _) -> compr (domf f) (domf $ faceMap f1) (unCube c f) (unCube c' f)
            (_, Minus, _) -> unCube c f
            (_, Plus, _) -> unCube c' f
    in Ne cd (Cube face) $ \i -> Comp k' (Act (cubeMapd rd) $ e i) (Act (cubeMapd rd') $ e' i)
compr n k (Spath p) (Spath p') = Spath $ compr (n + 1) k p p'
compr _ _ _ _ = error "compr"

pcon :: Integer -> Value -> Value
pcon n p = action (cubeMapd $ conMap $ n + 1) p

ppcon :: Integer -> Value -> Value
ppcon n (Spath p) = Spath $ Spath (pcon n p)
ppcon _ _ = error "pcon"

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
action m (Sid t a b) = Sid (action (liftc m) t) (action m a) (action m b)
action m v@(Stype _) = v
action m (Spath t) = Spath $ action (liftc m) t

reflect :: Integer -> Cube Value -> ITerm -> Value -> Value
reflect n (Cube c) e (Sid t a a') = Spath $ reflect (n + 1) (Cube face) e t
  where
    face f = case lastFace f of
                (f',Minus) -> action (cubeMapf f') a
                (f',Plus) -> action (cubeMapf f') a'
                (f',Zero) -> c f'
reflect _ (Cube c) e (Spi a (Slam x b)) = Slam x go
  where
    go m v | isDegMap m = reflect (domc m) (Cube $ \f -> go (composefd f $ degs m) (action (cubeMapf f) v))
                                           (\i -> appidp (degs m) (e i) $ reify i (domc m) v $ action m a) (b m v)
           | otherwise = app (domc m) (action (cubeMapd $ degs m) $ c $ faces m) v
    
    appidp :: DegMap -> Term -> Term -> Term
    appidp m x (Act m1 (Act m2 y)) = appidp m x $ Act (composec m1 m2) y
    appidp m x (Act m' y) =
        let (cm,_,rm,_) = commonDeg m (degs m') 0
        in Act (cubeMapd cm) $ App (domd rm) x $ Act (cubeMapc rm $ faces m') y
    appidp m x y = App (domd m) x y
reflect n (Cube c) e (Ssigma a b) =
    let e1 = reflect n (Cube $ \f -> proj1 (c f)) (\i -> App n Proj1 (e i)) a
    in Spair e1 $ reflect n (Cube $ \f -> proj2 (c f)) (\i -> App n Proj2 (e i)) (app n b e1)
reflect n c e _ = case e 0 of
    Act m _ -> Ne (degs m) c $ \i -> case e i of
        Act m' e' -> Act (cubeMapf $ faces m') e'
        _ -> error "reflect"
    _ -> Ne (idd n) c e

reflect0 :: ITerm -> Value -> Value
reflect0 = reflect 0 (error "reflect0")

reify :: DBIndex -> Integer -> Value -> Value -> Term
reify i n (Spath v) (Sid t _ _) = reify i (n + 1) v t
reify i n (Spath _) _ = error "reify.Spath"
reify i n (Slam x f) (Spi a b) =
    let v = svar i n a
    in Lam n [x] $ reify (i + 1) n (f (idc n) v) (app n b v)
reify _ _ (Slam _ _) _ = error "reify.Slam"
reify i n (Spair e1 e2) (Ssigma a b) = Pair (reify i n e1 a) (reify i n e2 $ app n b e1)
reify _ _ (Spair _ _) _ = error "reify.Spair"
reify _ n Szero Snat = iterate (App 0 Idp) (NatConst 0) `genericIndex` n
reify _ _ Szero _ = error "reify.Szero"
reify i n (Ssuc e) Snat = case dropIdps n (reify i n e Snat) of
    NatConst k -> iidp n $ NatConst (k + 1)
    t -> App n Suc t
  where iidp k x = iterate (App 0 Idp) x `genericIndex` k
        dropIdps n (App 0 Idp r) = dropIdps (n - 1) r
        dropIdps _ r = r
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
