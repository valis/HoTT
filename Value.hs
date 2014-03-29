module Value
    ( Value(..)
    , D(..), GlobMap
    , svar, gvar, sarr, sprod
    , Ctx, CtxV
    , ctxToCtxV
    , cmpTypes, cmpValues
    , isFreeVar
    , reify, reifyType
    , proj1, proj2, app, coe, pmap, trans
    , idf, idp, action, liftTerm, reduceD, lastD
    , inv, invIdp, comp
    ) where

import qualified Data.Map as M
import Data.List

import Syntax.Common
import Syntax.Term

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spair Value Value -- Constructor for Sigma-types
    | Spi String Value (Integer -> GlobMap -> Value -> Value) -- Constructor for Type_k
    | Ssigma String Value (Integer -> GlobMap -> Value -> Value) -- Constructor for Type_k
    | Snat | Sid Value Value Value | Stype Level -- Constructors for Type_k
    | Sidp Value -- Constructor for Id
    | Ne [(ITerm,ITerm)] ITerm
    | Swtype ITerm -- Wrapper for types
    | Siso Integer Value Value Value Value Value Value -- Higher constructor for Type_k
    -- | Scomp Value Value | Ssym Value
type Ctx  = (M.Map String (Value,Value), [(Value,Value)])
type CtxV = (M.Map String Value, [Value])

reduceD :: [D] -> [D]
reduceD [] = []
reduceD (Ld:ds) = Ld : reduceD ds
reduceD (Rd:ds) = Rd : reduceD ds
reduceD (Ud:ds) = case reduceD ds of
    Ld:ds' -> ds'
    Rd:ds' -> ds'
    ds' -> Ud:ds'

lastD :: [D] -> Maybe D
lastD = go . reduceD
  where
    go [] = Nothing
    go [d] = Just d
    go (_:ds) = go ds

infixr 5 `sarr`
sarr :: Value -> Value -> Value
sarr a b = Spi "_" a $ \k _ _ -> action (genericReplicate k Ud) b

sprod :: Value -> Value -> Value
sprod a b = Ssigma "_" a $ \k _ _ -> action (genericReplicate k Ud) b

ctxToCtxV :: Ctx -> CtxV
ctxToCtxV (ctx,vs) = (M.map fst ctx, map fst vs)

isFreeVar :: DBIndex -> DBIndex -> Value -> Bool
isFreeVar k i (Slam _ f) = isFreeVar (k + 1) (i + 1) $ f 0 [] $ Ne [] (\_ -> NoVar)
isFreeVar _ _ Szero = False
isFreeVar k i (Ssuc v) = isFreeVar k i v
isFreeVar k i (Spair a b) = isFreeVar k i a || isFreeVar k i b
isFreeVar k i (Spi _ a b) = isFreeVar k i a || isFreeVar (k + 1) (i + 1) (b 0 [] $ Ne [] $ \_ -> NoVar)
isFreeVar k i (Ssigma _ a b) = isFreeVar k i a || undefined isFreeVar (k + 1) (i + 1) (b 0 [] $ Ne [] $ \_ -> NoVar)
isFreeVar _ _ Snat = False
isFreeVar _ _ (Stype _) = False
isFreeVar k i (Sid t a b) = isFreeVar k i t || isFreeVar k i a || isFreeVar k i b
isFreeVar k i (Sidp v) = isFreeVar k i v
isFreeVar k i (Ne ts t) =
    any (\(l,r) -> elem k (freeLVars $ l i) || elem k (freeLVars $ r i)) ts || elem k (freeLVars $ t i)
isFreeVar k i (Swtype t) = elem k $ freeLVars (t i)
isFreeVar k i (Siso _ a b c d e f) = isFreeVar k i a || isFreeVar k i b || isFreeVar k i c
                                  || isFreeVar k i d || isFreeVar k i e || isFreeVar k i f

cmpTypes :: DBIndex -> Value -> Value -> Bool
cmpTypes i (Spi x a b)    (Spi _ a' b')    = cmpTypes i a' a && cmpTypes (i + 1) (b 0 [] $ svar i a) (b' 0 [] $ svar i a')
cmpTypes i (Ssigma x a b) (Ssigma _ a' b') = cmpTypes i a a' && cmpTypes (i + 1) (b 0 [] $ svar i a) (b' 0 [] $ svar i a')
cmpTypes i (Sid t a b) (Sid t' a' b') = cmpTypes i t t' && cmpValues i a a' t && cmpValues i b b' t
cmpTypes _ Snat Snat = True
cmpTypes _ (Stype k) (Stype k') = k <= k'
cmpTypes i s@(Siso n a b c d e f) s'@(Siso n' a' b' c' d' e' f') =
    n == n' && cmpTypes i a a' && cmpTypes i b b' && cmpValues i c c' (a `sarr` b) && cmpValues i d d' (b `sarr` a)
    && reifySiso5 i s == reifySiso5 i s' && reifySiso6 i s == reifySiso6 i s'
cmpTypes l (Swtype t) (Swtype t') = t l == t' l
cmpTypes _ _ _ = False

cmpValues :: DBIndex -> Value -> Value -> Value -> Bool
cmpValues i e1 e2 t = reify i e1 t == reify i e2 t

svar :: DBIndex -> Value -> Value
svar i = liftTerm $ \l -> LVar (l - i - 1)

gvar :: String -> Value -> Value
gvar v = liftTerm $ \_ -> Var v

proj1 :: Value -> Value
proj1 (Spair a _) = a
proj1 _ = error "proj1"

proj2 :: Value -> Value
proj2 (Spair _ b) = b
proj2 _ = error "proj1"

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) a = f n [] a
app _ _ _ = error "Value.app"

coe :: Value -> Value
coe (Siso _ _ _ f _ _ _) = f
coe _ = error "coe"

pmap :: Integer -> Value -> Value -> Value
pmap n = app (n + 1)

trans :: Integer -> Value -> Value -> Value -> Value
trans n b p = app n (coe $ pmap n (idp n b) p)

getBase :: Value -> (Integer,Value)
getBase (Sid t _ _) = let (n,r) = getBase t in (n + 1, r)
getBase r = (0,r)

liftTerm :: ITerm -> Value -> Value
liftTerm e t | App Idp _ <- e 0 = case t of
    Sid t' _ _-> action [Ud] $ flip liftTerm t' $ \i -> case e i of
        App Idp e -> e
        _ -> error "liftTerm.Idp"
    _ -> error "liftTerm.Idp.Id"
liftTerm e t | (n,Stype _) <- getBase t = case t of
    Stype _ -> Swtype e
    Sid _ a b -> Siso n a b
        (liftTerm (\l -> App (iterate (App Pmap . App Idp) Coe `genericIndex` (n - 1)) (e l)) $ go t n)
        (liftTerm
            (\l -> if n == 1
                    then App Inv $ App Coe (e l)
                    else App (iterate (App Pmap . App Idp) term `genericIndex` (n - 2)) (e l)
            ) $ goRev t n)
        (error "TODO: liftTerm.Siso.1")
        (error "TODO: liftTerm.Siso.2")
    _ -> error "liftTerm.Stype"
  where
    term = App Pmap $ Lam ["x"] $ App Idp $ App Inv $ App Coe (LVar 0)
    
    go (Sid _ a b) 1 = a `sarr` b
    go (Sid t p q) n =
        let r = iterate (App Pmap . App Idp) Coe `genericIndex` (n - 2)
            t' = go t (n - 1)
        in Sid t' (liftTerm (\l -> App r $ reify l p t) t') (liftTerm (\l -> App r $ reify l q t) t')
    go _ _ = error "liftTerm.Stype.go"
    
    goRev (Sid _ a b) 1 = b `sarr` a
    goRev (Sid t p q) 2 =
        let t' = goRev t 1
            a' l = App Inv $ App Coe (reify l p t)
            b' l = App Inv $ App Coe (reify l q t)
        in Sid t' (liftTerm a' t') (liftTerm b' t')
    goRev (Sid t p q) n = 
        let r = iterate (App Pmap . App Idp) term `genericIndex` (n - 3)
            t' = goRev t (n - 1)
        in Sid t' (liftTerm (\l -> App r $ reify l p t) t') (liftTerm (\l -> App r $ reify l q t) t')
    goRev _ _ = error "liftTerm.goRev"
liftTerm e t | (n, Spi x a b) <- getBase t = Slam x $ \k m v ->
    go a (b 0 [] $ action (genericReplicate k Rd) v) (\l -> actionTerm m $ iterate (App Pmap) (e l) `genericIndex` n) k v
  where
    actionTerm :: [D] -> Term -> Term
    actionTerm [] e = e
    actionTerm (Ud:a) e = actionTerm a $ App Pmap (App Idp e)
    actionTerm (_:a) (App Pmap (App Idp e)) = actionTerm a e
    actionTerm _ _ = error "Value.actionTerm"
    
    go a b e' k v = liftTerm (\l -> appTerm (e' l) $ reify l v $ liftTypeValue k v a) (goType k v)
      where
        liftTypeValue 0 _ a = a
        liftTypeValue k v a = Sid (liftTypeValue (k - 1) (action [Ld] v) a) (action [Ld] v) (action [Rd] v)
        
        appTerm (App Pmap (App Idp e1)) (App Idp e2) = App Idp (appTerm e1 e2)
        appTerm e1 e2 = App e1 e2
        
        goType 0 _ = b
        goType k v = Sid (goType (k - 1) (action [Ld] v)) (go a b e' (k - 1) $ action [Ld] v)
                                                          (go a b e' (k - 1) $ action [Rd] v)
liftTerm e t | (n,Ssigma _ a b) <- getBase t = case n of
    0 -> let a' = liftTerm (App Proj1 . e) a
         in Spair a' $ liftTerm (App Proj2 . e) (b 0 [] a')
    n -> error $ "TODO: liftTerm.Ssigma: " ++ show n
liftTerm e t = Ne (sidToList t) e
  where
    sidToList :: Value -> [(ITerm,ITerm)]
    sidToList (Sid t a b) = (\l -> liftTermDB l (reify 0 a t), \l -> liftTermDB l (reify 0 b t)) : sidToList t
    sidToList _ = []

inv :: Integer -> Value -> Value
inv 0 r@(Sidp _) = r
inv 0 (Siso 1 a b f g p q) = Siso 1 b a g f q p
inv 0 (Siso k a b (Slam xf ef) (Slam xg eg) p q) = Siso k a b
    (Slam xf $ \k m v -> inv 0 $ ef k m v) -- TODO: ???
    (Slam xg $ \k m v -> inv 0 $ eg k m v) -- TODO: ???
    (error "TODO: inv.Siso.1") (error "TODO: inv.Siso.2")
inv 0 (Slam x f) = Slam x $ \k m v -> inv k $ f k m (inv k v)
inv 0 (Ne ((l,r):t) e) = Ne ((r,l):t) (App Inv . e)
inv 0 (Spair _ _) = error "TODO: inv.Spair"
inv _ Szero = Szero
inv _ s@(Ssuc _) = s
inv 1 r@(Sidp (Sidp _)) = r
inv 1 (Siso k _ _ _ _ _ _) = error $ "TODO: inv.Siso: " ++ show (1,k)
inv 1 (Sidp (Ne [(a,b)] e)) = Sidp $ Ne [(b,a)] (App Inv . e)
inv 1 (Ne [(l,r),(a,b)] e) = Ne [(App Inv . l, App Inv . r), (b,a)] (App Pmap . App (Idp `App` Inv) . e)
inv n _ = error $ "TODO: inv: " ++ show n

invIdp :: Integer -> Value -> Value
invIdp 0 x@(Sidp _) = Sidp x
invIdp _ (Slam x f) = Slam x $ \k _ -> invIdp k
invIdp 0 (Siso 1 a b f g p q) = Siso 2 b b q q (error "TODO: invIdp.Siso.1") (error "TODO: invIdp.Siso.2")
invIdp 0 (Ne [(l,r)] e) = Ne [(\i -> Comp `App` App Inv (e i) `App` e i, App Idp . r), (r,r)] (App InvIdp . e)
invIdp n _ = error $ "TODO: invIdp: " ++ show n

comp :: Integer -> Value -> Value -> Value
comp _ (Slam x f) (Slam _ g) = Slam x $ \k m v -> comp k (f k m $ action [Ld,Ud] v) (g k m v)
comp 0 (Sidp _) x = x
comp 0 x (Sidp _) = x
comp 0 (Ne ((l,_):t1) e1) (Ne ((_,r):t2) e2) = Ne ((l,r):maxList t1 t2) $ \i -> Comp `App` e1 i `App` e2 i
  where maxList t [] = t
        maxList [] t = t
        maxList (x:xs) (_:ys) = x : maxList xs ys
comp 1 (Sidp (Sidp _)) x = x
comp 1 x (Sidp (Sidp _)) = x
comp 1 (Sidp (Ne [(a,_)] e1)) (Sidp (Ne [(_,b)] e2)) = Sidp $ Ne [(a,b)] $ \l -> Comp `App` e1 l `App` e2 l
comp 1 (Sidp (Ne [(a,_)] e1)) (Ne [(l2,r2),(_,b)] e2) =
    Ne [(\i -> Comp `App` e1 i `App` l2 i, \i -> Comp `App` e1 i `App` r2 i),(a,b)] $
        \i -> Pmap `App` (App Idp $ Comp `App` e1 i) `App` e2 i
comp 1 x (Sidp (Ne l e1)) = comp 1 x (Ne ((e1,e1):l) $ App Idp . e1)
comp 1 (Ne [(l1,r1),(a,_)] e1) (Ne [(l2,r2),(_,b)] e2) =
    Ne [(\i -> Comp `App` l1 i `App` l2 i, \i -> Comp `App` r1 i `App` r2 i),(a,b)] $
        \i -> Pmap `App` (Pmap `App` App Idp Comp `App` e1 i) `App` e2 i
comp n _ _ = error $ "TODO: comp: " ++ show n

idp :: Integer -> Value -> Value
idp 0 v = action [Ud] v
idp 1 v = invIdp 0 v
idp n _ = error $ "TODO: idp: " ++ show n

idf :: Value
idf = Slam "x" $ \_ _ -> id

action :: GlobMap -> Value -> Value
action [] v = v
action m (Slam x f) = Slam x (\k n -> f k (n ++ m))
action m (Spair e1 e2) = Spair (action m e1) (action m e2) -- TODO: This is incorrect.
action _ Szero = Szero
action _ v@(Ssuc _) = v
action (Ud:m) t@(Spi _ _ _) = action m (Siso 1 t t idf idf idf idf)
action (Ud:m) t@(Ssigma _ _ _) = action m (Siso 1 t t idf idf idf idf)
action (Ud:m) Snat = action m (Siso 1 Snat Snat idf idf idf idf)
action (Ud:m) t@(Sid _ _ _) = action m (Siso 1 t t idf idf idf idf)
action (Ud:m) t@(Stype _) = action m (Siso 1 t t idf idf idf idf)
action (Ud:m) t@(Swtype _) = action m (Siso 1 t t idf idf idf idf)
action (Ld:m) (Siso 1 a _ _ _ _ _) = action m a
action (Rd:m) (Siso 1 _ b _ _ _ _) = action m b
action (Ud:m) (Siso n a b f g p q) = action m $ Siso (n + 1) a b (action [Ud] f) (action [Ud] g)
    (error "TODO: action.Siso.1") (error "TODO: action.Siso.2")
action ( d:m) (Siso n a b f g p q) = action m $ Siso (n - 1) a b (action [ d] f) (action [ d] g)
    (error "TODO: action.Siso.3") (error "TODO: action.Siso.4")
action (Ld:m) (Sidp x) = action m x
action (Rd:m) (Sidp x) = action m x
action (Ud:m) v = action m (Sidp v)
action (Ld:m) (Ne ((l,_):t) e) = action m (Ne t l)
action (Ld:m) (Ne [] e) = error "action.Ld.Ne"
action (Rd:m) (Ne ((_,r):t) e) = action m (Ne t r)
action (Rd:m) (Ne [] e) = error "action.Rd.Ne"
action _ (Spi _ _ _) = error "action.Spi"
action _ (Ssigma _ _ _) = error "action.Ssigma"
action _ Snat = error "action.Snat"
action _ (Sid _ _ _) = error "action.Sid"
action _ (Stype _) = error "action.Stype"
action _ (Swtype _) = error "action.Swtype"

reify :: DBIndex -> Value -> Value -> Term
reify i (Slam x f) (Spi _ a b) =
    let v = svar i a
    in Lam [x] $ reify (i + 1) (f 0 [] v) (b 0 [] v)
reify i (Slam _ h) (Sid t@(Spi x a b) f g) =
    let v0 = svar i a
        v1 = idp 0 v0
    in App (Ext (reify i f t) (reify i g t)) $ Lam [x] $ reify (i + 1) (h 1 [] v1) $
        Sid (b 0 [] v0) (app 0 f v0) (app 0 g v0)
reify i (Slam _ h) (Sid t@(Sid t'@(Spi x a b) f' g') f g) =
    let v0 = svar i a
        v1 = idp 0 v0
        v2 = idp 1 v1
    in App (App Pmap $ App Idp (Ext (reify i f' t') (reify i g' t'))) $
        App (Ext (reify i f t) (reify i g t)) $ Lam [x] $ reify (i + 1) (h 2 [] v2) $
        Sid (Sid (b 0 [] v0) (app 0 f' v0) (app 0 g' v0)) (app 1 f v1) (app 1 g v1)
reify _ (Slam _ _) _ = error "reify.Slam"
reify i (Spair e1 e2) (Ssigma _ a b) = Pair (reify i e1 a) (reify i e2 $ b 0 [] e1)
reify i (Spair e1 e2) (Sid t@(Ssigma _ a b) p q) = ExtSigma (reify i p t) (reify i q t) `App`
    Pair (reify i e1 $ Sid a (proj1 p) (proj1 q))
         (reify i e2 $ Sid (b 0 [] $ action [Rd] e1) (action [Ld] e1) (action [Rd] e2))
reify _ (Spair _ _) t | (n, Ssigma _ _ _) <- getBase t = error $ "TODO: reify.Spair: " ++ show n
reify _ (Spair _ _) _ = error "reify.Spair"
reify i (Swtype e) (Stype _) = e i
reify _ (Swtype _) _ = error "reify.Swtype"
reify i s@(Siso 1 a b c d _ _) (Sid (Stype _) _ _) = Iso `App` reifyType i a `App` reifyType i b
    `App` reify i c (a `sarr` b) `App` reify i d (b `sarr` a) `App` reifySiso5 i s `App` reifySiso6 i s
reify _ (Siso n a b c d e f) _ = error $ "TODO: reify.Siso: " ++ show n
reify _ (Szero) t | (n, Snat) <- getBase t = iterate (App Idp) (NatConst 0) `genericIndex` n
reify _ (Szero) _ = error "reify.Szero"
reify i (Ssuc e) t | (n, Snat) <- getBase t = iidp n $ case reify i e Snat of
    NatConst n -> NatConst (n + 1)
    t -> App Suc t
  where iidp n x = iterate (App Idp) x `genericIndex` n
reify _ (Ssuc _) _ = error "reify.Ssuc"
reify i (Spi x a b) u@(Stype _) = Pi [([x],reify i a u)] $ reify (i + 1) (b 0 [] $ svar i a) u
reify _ (Spi _ _ _) _ = error "reify.Spi"
reify i (Ssigma x a b) u@(Stype _) = Sigma [([x],reify i a u)] $ reify (i + 1) (b 0 [] $ svar i a) u
reify _ (Ssigma _ _ _) _ = error "reify.Ssigma"
reify i (Sid t a b) u@(Stype _) = Id (reify i t u) (reify i a t) (reify i b t)
reify _ (Sid _ _ _) _ = error "reify.Sid"
reify _ (Stype u) (Stype _) = Universe u
reify _ (Stype _) _ = error "reify.Stype"
reify _ (Snat) (Stype _) = Nat
reify _ (Snat) _ = error "reify.Snat"
reify i (Sidp x) (Sid t _ _) = App Idp (reify i x t)
reify _ (Sidp _) _ = error "reify.Sidp"
reify i (Ne _ e) _ = e i

reifyType :: DBIndex -> Value -> Term
reifyType i t = reify i t (Stype maxBound)

reifySiso5 :: DBIndex -> Value -> Term
reifySiso5 i (Siso _ a b c d e f) = reify i e $ Spi "x" a $ \_ _ v -> Sid b (app 0 d $ app 0 c v) v
reifySiso5 _ _ = error "reifySiso5"

reifySiso6 :: DBIndex -> Value -> Term
reifySiso6 i (Siso _ a b c d e f) = reify i f $ Spi "x" b $ \_ _ v -> Sid a (app 0 c $ app 0 d v) v
reifySiso6 _ _ = error "reifySiso6"
