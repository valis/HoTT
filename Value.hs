module Value
    ( Value(..)
    -- , SisoData(..)
    , D(..), GlobMap
    , svar, gvar, sarr, sprod
    , Ctx, CtxV
    , ctxToCtxV
    , cmpTypes, cmpValues
    , isFreeVar
    , reify, reifyType
    , proj1, proj2, app, coe, pmap, trans
    , idf, idp, action, reflect, reduceD, lastD
    , inv, invIdp, comp
    ) where

import qualified Data.Map as M
import Data.List

import Syntax.Common
import Syntax.Term

{-
data SisoData = SisoData
    { sisoLeft :: Value                     -- A : Type
    , sisoRight :: Value                    -- B : Type
    , sisoLR :: Value                       -- f : A -> B
    , sisoRL :: Value                       -- g : B -> A
    , sisoLI :: Value                       -- (a : A) -> g (f a) = a
    , sisoRI :: Value                       -- (b : B) -> f (g b) = b
    , sisoInv :: Integer -> Value -> Value  -- x = y | self -> y = x | inv self
    , sisoOver :: Value -> Value -> Value
    }
-}

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spair Value Value -- Constructor for Sigma-types
    | Spi Integer String Value (Integer -> GlobMap -> Value -> Value) -- Constructor for Type_k
    | Ssigma Integer String Value (Integer -> GlobMap -> Value -> Value) -- Constructor for Type_k
    | Snat | Stype Level -- Constructors for Type_k
    | Sid Integer Value Value Value
    -- | SidOver Value Value ITerm
    | Sidp Value -- Constructor for Id
    | Ne [(ITerm,ITerm)] ITerm
    | Swtype [(Value,Value)] ITerm -- Wrapper for types
    {-
    | Siso1 SisoData -- 1-constructor for Type_k
    | Siso Integer Value Value Value Value Value Value -- Higher constructor for Type_k
    -}
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

lengthD :: [D] -> Integer
lengthD [] = 0
lengthD (Ud:m) = lengthD m + 1
lengthD (_:m) = lengthD m - 1

sarr :: Integer -> Value -> Value -> Value
sarr n a b = Spi n "_" a $ \k _ _ -> action (genericReplicate k Ud) b

sprod :: Integer -> Value -> Value -> Value
sprod n a b = Ssigma n "_" a $ \k _ _ -> action (genericReplicate k Ud) b

ctxToCtxV :: Ctx -> CtxV
ctxToCtxV (ctx,vs) = (M.map fst ctx, map fst vs)

isFreeVar :: DBIndex -> DBIndex -> Value -> Bool
isFreeVar k i (Slam _ f) = isFreeVar (k + 1) (i + 1) $ f 0 [] $ Ne [] (\_ -> NoVar)
isFreeVar _ _ Szero = False
isFreeVar k i (Ssuc v) = isFreeVar k i v
isFreeVar k i (Spair a b) = isFreeVar k i a || isFreeVar k i b
isFreeVar k i (Spi n _ a b) = isFreeVar k i a || isFreeVar (k + 1) (i + 1) (b n [] $ Ne [] $ \_ -> NoVar)
isFreeVar k i (Ssigma n _ a b) = isFreeVar k i a || undefined isFreeVar (k + 1) (i + 1) (b n [] $ Ne [] $ \_ -> NoVar)
isFreeVar _ _ Snat = False
isFreeVar _ _ (Stype _) = False
isFreeVar k i (Sid _ t a b) = isFreeVar k i t || isFreeVar k i a || isFreeVar k i b
isFreeVar k i (Sidp v) = isFreeVar k i v
isFreeVar k i (Ne ts t) =
    any (\(l,r) -> elem k (freeLVars $ l i) || elem k (freeLVars $ r i)) ts || elem k (freeLVars $ t i)
isFreeVar k i (Swtype ts t) = any (\(l,r) -> isFreeVar k i l || isFreeVar k i r) ts || elem k (freeLVars $ t i)
{-
isFreeVar k i (Siso1 s) = isFreeVar k i (sisoLeft s) || isFreeVar k i (sisoRight s) || isFreeVar k i (sisoLR s)
                       || isFreeVar k i (sisoRL s)   || isFreeVar k i (sisoLI s)    || isFreeVar k i (sisoRI s)
isFreeVar k i (Siso _ a b c d e f) = isFreeVar k i a || isFreeVar k i b || isFreeVar k i c
                                  || isFreeVar k i d || isFreeVar k i e || isFreeVar k i f
-}

cmpTypes :: DBIndex -> Value -> Value -> Bool
cmpTypes i (Spi n x a b) (Spi n' _ a' b') =
    n == n' && cmpTypes i a' a && cmpTypes (i + 1) (b n [] $ svar i a) (b' n [] $ svar i a')
cmpTypes i (Ssigma n x a b) (Ssigma n' _ a' b') =
    n == n' && cmpTypes i a a' && cmpTypes (i + 1) (b n [] $ svar i a) (b' n [] $ svar i a')
cmpTypes i (Sid n t a b) (Sid n' t' a' b') = n == n' && cmpTypes i t t' && cmpValues i a a' t && cmpValues i b b' t
cmpTypes _ Snat Snat = True
cmpTypes _ (Stype k) (Stype k') = k <= k'
cmpTypes i (Ne _ e) (Ne _ e') = e i == e' i
{-
cmpTypes i (Siso1 s@SisoData{ sisoLeft = a, sisoRight = b }) (Siso1 s'@SisoData{ sisoLeft = a', sisoRight = b' }) =
    cmpTypes i a a' && cmpTypes i b b' &&
    cmpValues i (sisoLR s) (sisoLR s') (a `sarr` b) && cmpValues i (sisoRL s) (sisoRL s') (b `sarr` a) &&
    reifySiso5 i (Siso1 s) == reifySiso5 i (Siso1 s') && reifySiso6 i (Siso1 s) == reifySiso6 i (Siso1 s')
cmpTypes i s@(Siso n a b c d e f) s'@(Siso n' a' b' c' d' e' f') =
    -- TODO: Fix this.
    n == n' && cmpTypes i a a' && cmpTypes i b b' && cmpValues i c c' (a `sarr` b) && cmpValues i d d' (b `sarr` a)
    && reifySiso5 i s == reifySiso5 i s' && reifySiso6 i s == reifySiso6 i s'
-}
cmpTypes l (Swtype _ t) (Swtype _ t') = t l == t' l
cmpTypes _ _ _ = False

cmpValues :: DBIndex -> Value -> Value -> Value -> Bool
cmpValues i e1 e2 t = reify i e1 t == reify i e2 t

svar :: DBIndex -> Value -> Value
svar i = reflect $ \l -> LVar (l - i - 1)

gvar :: String -> Value -> Value
gvar v = reflect $ \_ -> Var v

proj1 :: Value -> Value
proj1 (Spair a _) = a
proj1 _ = error "proj1"

proj2 :: Value -> Value
proj2 (Spair _ b) = b
proj2 _ = error "proj1"

app :: Integer -> Value -> Value -> Value
app n (Slam _ f) a = f n [] a
app _ _ _ = error "Value.app"

fibrLifting :: Integer -> Value -> Value -> Value
fibrLifting n _ _ = error $ "TODO: fibrLifting: " ++ show n

opfibrLifting :: Integer -> Value -> Value -> Value
opfibrLifting n _ _ = error $ "TODO: opfibrLifting: " ++ show n

coe :: Integer -> Value -> Value
{-
coe (Siso1 s) = sisoLR s
coe (Siso _ _ _ f _ _ _) = f
-}
coe n (Spi _ _ a b) = Slam "f" $ \_ m' f -> Slam "x" $ \k m x ->
    app k (coe k $ b k m $ fibrLifting k (action m a) x) $ app k (action m f) $ app k (action m $ coe n $ inv n a) x
coe n (Ssigma _ _ a b) = Slam "p" $ \k m p -> Spair (app k (action m $ coe n a) $ proj1 p) $
    app k (coe k $ b k m $ opfibrLifting k (action m a) $ proj1 p) (proj2 p)
coe n (Sid k t a b) = error $ "TODO: coe.Sid: " ++ show (n,k)
coe _ Snat = idf
coe _ (Stype _) = idf
coe 0 (Sidp _) = idf
coe n (Sidp t) = action [Ud] $ coe (n - 1) t
coe n (Swtype l e) = reflect (App (iterate (App Pmap . App Idp) Coe `genericIndex` n) . e) (go n l)
  where
    go 0 [(a,b)] = sarr 0 a b
    go n ((a,b):t) = Sid 0 (go (n - 1) t) (coe (n - 1) a) (coe (n - 1) b)
    go n _ = error $ "coe.Swtype: " ++ show n
coe _ _ = error "coe"

pmap :: Integer -> Value -> Value -> Value
pmap n = app (n + 1)

trans :: Integer -> Value -> Value -> Value -> Value
trans n b p = app n (coe n $ pmap n (idp n b) p)

getBase :: Value -> (Integer,Value)
getBase (Sid 0 t _ _) = let (n,r) = getBase t in (n + 1, r)
getBase r = (0,r)

reflect :: ITerm -> Value -> Value
reflect e t | App Idp _ <- e 0 = case t of
    Sid 0 t' _ _-> action [Ud] $ flip reflect t' $ \i -> case e i of
        App Idp e -> e
        _ -> error "reflect.Idp"
    _ -> error "reflect.Idp.Id"
reflect e t | (n,Stype _) <- getBase t = Swtype (go t) e
  where
    go (Sid _ t a b) = (a,b) : go t
    go _ = []
{-
    Sid (Stype _) a b -> Siso1 $ SisoData
        { sisoLeft = a
        , sisoRight = b
        , sisoLR = reflect (\l -> App Coe (e l)) (a `sarr` b)
        , sisoRL = reflect (\l -> App Inv $ App Coe (e l)) (b `sarr` a)
        , sisoLI = error "TODO: reflect.Siso1.LI"
        , sisoRI = error "TODO: reflect.Siso1.RI"
        , sisoInv = error "TODO: reflect.Siso1.Inv"
        , sisoOver = error "TODO: reflect.Siso1.Over"
        }
    Sid _ a b -> Siso n a b
        (reflect (\l -> App (iterate (App Pmap . App Idp) Coe `genericIndex` (n - 1)) (e l)) $ go t n)
        (reflect (\l -> App (iterate (App Pmap . App Idp) term `genericIndex` (n - 2)) (e l)) $ goRev t n)
        (error "TODO: reflect.Siso.1")
        (error "TODO: reflect.Siso.2")
    _ -> error "reflect.Stype"
  where
    term = App Pmap $ Lam ["x"] $ App Idp $ App Inv $ App Coe (LVar 0)
    
    go (Sid _ a b) 1 = a `sarr` b
    go (Sid t p q) n =
        let r = iterate (App Pmap . App Idp) Coe `genericIndex` (n - 2)
            t' = go t (n - 1)
        in Sid t' (reflect (\l -> App r $ reify l p t) t') (reflect (\l -> App r $ reify l q t) t')
    go _ _ = error "reflect.Stype.go"
    
    goRev (Sid _ a b) 1 = b `sarr` a
    goRev (Sid t p q) 2 =
        let t' = goRev t 1
            a' l = App Inv $ App Coe (reify l p t)
            b' l = App Inv $ App Coe (reify l q t)
        in Sid t' (reflect a' t') (reflect b' t')
    goRev (Sid t p q) n = 
        let r = iterate (App Pmap . App Idp) term `genericIndex` (n - 3)
            t' = goRev t (n - 1)
        in Sid t' (reflect (\l -> App r $ reify l p t) t') (reflect (\l -> App r $ reify l q t) t')
    goRev _ _ = error "reflect.goRev"
-}
reflect e t | (n, Spi 0 x a b) <- getBase t = Slam x $ \k m v ->
    go a (b 0 [] $ action (genericReplicate k Rd) v) (\l -> actionTerm m $ iterate (App Pmap) (e l) `genericIndex` n) k v
  where
    actionTerm :: [D] -> Term -> Term
    actionTerm [] e = e
    actionTerm (Ud:a) e = actionTerm a $ App Pmap (App Idp e)
    actionTerm (_:a) (App Pmap (App Idp e)) = actionTerm a e
    actionTerm _ _ = error "Value.actionTerm"
    
    go a b e' k v = reflect (\l -> appTerm (e' l) $ reify l v $ liftTypeValue k v a) (goType k v)
      where
        liftTypeValue 0 _ a = a
        liftTypeValue k v a = Sid 0 (liftTypeValue (k - 1) (action [Ld] v) a) (action [Ld] v) (action [Rd] v)
        
        appTerm (App Pmap (App Idp e1)) (App Idp e2) = App Idp (appTerm e1 e2)
        appTerm e1 e2 = App e1 e2
        
        goType 0 _ = b
        goType k v = Sid 0 (goType (k - 1) (action [Ld] v)) (go a b e' (k - 1) $ action [Ld] v)
                                                            (go a b e' (k - 1) $ action [Rd] v)
reflect e t | (n,Ssigma 0 _ a b) <- getBase t = case n of
    0 -> let a' = reflect (App Proj1 . e) a
         in Spair a' $ reflect (App Proj2 . e) (b 0 [] a')
    n -> error $ "TODO: reflect.Ssigma: " ++ show n
reflect e t = Ne (sidToList t) e
  where
    sidToList :: Value -> [(ITerm,ITerm)]
    sidToList (Sid 0 t a b) = (\l -> liftTermDB l (reify 0 a t), \l -> liftTermDB l (reify 0 b t)) : sidToList t
    sidToList _ = []

inv :: Integer -> Value -> Value
inv 0 r@(Sidp _) = r
inv n (Sidp x) = Sidp $ inv (n - 1) x
inv _ (Slam x f) = Slam x $ \k m v -> inv k $ f k m (inv k v)
inv n (Ne t e) = Ne (invList n t) (invTerm n e)
  where
    invTerm n e i = genericIndex (iterate (App Pmap . App Idp) Inv) n `App` e i
    invList _ [] = error "inv.Ne.invList"
    invList 0 ((a,b):t) = (b,a):t
    invList n ((a,b):t) = (invTerm (n - 1) a, invTerm (n - 1) b) : invList (n - 1) t
inv n (Spair a b) = Spair (inv n a) (inv n b)
inv _ Szero = Szero
inv _ s@(Ssuc _) = s
inv n (Spi k _ a b) = error $ "TODO: inv.Spi: " ++ show (n,k)
inv n (Ssigma k _ a b) = error $ "TODO: inv.Ssigma: " ++ show (n,k)
inv n (Sid k _ a b) = error $ "TODO: inv.Sid: " ++ show (n,k)
inv n Snat = error $ "TODO: inv.Snat: " ++ show n
inv n (Stype _) = error $ "TODO: inv.Stype: " ++ show n
inv n (Swtype _ _) = error $ "TODO: inv.Swtype: " ++ show n
{-
inv 0 (Siso1 s) = Siso1 $ s -- TODO: Fix this.
    { sisoLeft = sisoRight s
    , sisoRight = sisoLeft s
    , sisoLR = sisoRL s
    , sisoRL = sisoLR s
    , sisoLI = sisoRI s
    , sisoRI = sisoLI s
    }
inv 0 (Siso k a b (Slam xf ef) (Slam xg eg) p q) = Siso k a b
    (Slam xf $ \k m v -> inv 0 $ ef k m v) -- TODO: ???
    (Slam xg $ \k m v -> inv 0 $ eg k m v) -- TODO: ???
    (error "TODO: inv.Siso.1") (error "TODO: inv.Siso.2")
inv n (Siso1 _) = error $ "TODO: inv.Siso1: " ++ show n
inv n (Siso k _ _ _ _ _ _) = error $ "TODO: inv.Siso: " ++ show (n,k)
-}

invIdp :: Integer -> Value -> Value
invIdp 0 x@(Sidp _) = Sidp x
invIdp _ (Slam x f) = Slam x $ \k _ -> invIdp k
{-
invIdp 0 (Siso1 s) =
    Siso 2 (Siso1 s) (Siso1 s) (sisoRI s) (sisoRI s) (error "TODO: invIdp.Siso.1") (error "TODO: invIdp.Siso.2")
-}
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
idp _ = action [Ud]

idf :: Value
idf = Slam "x" $ \_ _ -> id

action :: GlobMap -> Value -> Value
action [] v = v
action m (Slam x f) = Slam x (\k n -> f k (n ++ m))
action m (Spair e1 e2) = Spair (action m e1) (action m e2) -- TODO: This is incorrect.
action _ Szero = Szero
action _ v@(Ssuc _) = v
action (Ld:m) (Sidp x) = action m x
action (Rd:m) (Sidp x) = action m x
action (Ld:m) (Ne ((l,_):t) e) = action m (Ne t l)
action (Ld:m) (Ne [] e) = error "action.Ld.Ne"
action (Rd:m) (Ne ((_,r):t) e) = action m (Ne t r)
action (Rd:m) (Ne [] e) = error "action.Rd.Ne"
action m t@(Spi _ _ _ _) = actionType m t
action m t@(Ssigma _ _ _ _) = actionType m t
action m Snat = actionType m Snat
action m t@(Sid _ _ _ _) = actionType m t
action m t@(Stype _) = actionType m t
action m t@(Swtype _ _) = actionType m t
{-
action m t@(Siso1 _) = actionType m t
action m t@(Siso _ _ _ _ _ _ _) = actionType m t
-}
action (Ud:m) v = action m (Sidp v)

actionType :: GlobMap -> Value -> Value
actionType [] t = t
actionType m (Spi n x a b)    = Spi    (n + lengthD m) x (action m a) (\k m' -> b k (m' ++ m))
actionType m (Ssigma n x a b) = Ssigma (n + lengthD m) x (action m a) (\k m' -> b k (m' ++ m))
actionType m (Sid n t a b)    = Sid    (n + lengthD m) t (action m a) (action m b)
actionType _ Snat             = Snat
actionType _ t@(Stype _)      = t
actionType (Ld:m) (Swtype ((a,_):_) _) = action m a
actionType (Rd:m) (Swtype ((_,b):_) _) = action m b
actionType (Ud:m) t@(Swtype _ _) = action m (Sidp t)
{-
actionType (Ld:m) (Siso1 s) = action m (sisoLeft s)
actionType (Rd:m) (Siso1 s) = action m (sisoRight s)
actionType (Ud:m) (Siso1 s) = actionType m $ Siso 2 (Siso1 s) (Siso1 s) (action [Ud] $ sisoLR s) (action [Ud] $ sisoRL s)
    (error "TODO: actionType.Siso1.1") (error "TODO: actionType.Siso1.2")
actionType (Ld:m) (Siso 2 a _ _ _ _ _) = actionType m a
actionType (Rd:m) (Siso 2 _ b _ _ _ _) = actionType m b
actionType (Ud:m) (Siso n a b f g p q) = actionType m $ Siso (n + 1) a b (action [Ud] f) (action [Ud] g)
    (error "TODO: actionType.Siso.1") (error "TODO: actionType.Siso.2")
actionType ( d:m) (Siso n a b f g p q) = actionType m $ Siso (n - 1) a b (action [ d] f) (action [ d] g)
    (error "TODO: actionType.Siso.3") (error "TODO: actionType.Siso.4")
actionType (Ud:m) t = actionType m $ Siso1 $ SisoData
    { sisoLeft = t
    , sisoRight = t
    , sisoLR = idf
    , sisoRL = idf
    , sisoLI = idf
    , sisoRI = idf
    , sisoInv = error "TODO: actionType.Inv"
    , sisoOver = error "TODO: actionType.Over"
    }
-}
actionType _ _ = error "actionType"

reify :: DBIndex -> Value -> Value -> Term
reify i (Slam x f) (Spi 0 _ a b) =
    let v = svar i a
    in Lam [x] $ reify (i + 1) (f 0 [] v) (b 0 [] v)
reify i (Slam _ h) (Sid 0 t@(Spi 0 x a b) f g) =
    let v0 = svar i a
        v1 = idp 0 v0
    in App (Ext (reify i f t) (reify i g t)) $ Lam [x] $ reify (i + 1) (h 1 [] v1) $
        Sid 0 (b 0 [] v0) (app 0 f v0) (app 0 g v0)
reify i (Slam _ h) (Sid 0 t@(Sid 0 t'@(Spi 0 x a b) f' g') f g) =
    let v0 = svar i a
        v1 = idp 0 v0
        v2 = idp 1 v1
    in App (App Pmap $ App Idp (Ext (reify i f' t') (reify i g' t'))) $
        App (Ext (reify i f t) (reify i g t)) $ Lam [x] $ reify (i + 1) (h 2 [] v2) $
        Sid 0 (Sid 0 (b 0 [] v0) (app 0 f' v0) (app 0 g' v0)) (app 1 f v1) (app 1 g v1)
reify _ (Slam _ _) _ = error "reify.Slam"
reify i (Spair e1 e2) (Ssigma 0 _ a b) = Pair (reify i e1 a) (reify i e2 $ b 0 [] e1)
reify i (Spair e1 e2) (Sid 0 t@(Ssigma 0 _ a b) p q) = ExtSigma (reify i p t) (reify i q t) `App`
    Pair (reify i e1 $ Sid 0 a (proj1 p) (proj1 q))
         (reify i e2 $ Sid 0 (b 0 [] $ action [Rd] e1) (action [Ld] e1) (action [Rd] e2))
reify _ (Spair _ _) t | (n, Ssigma 0 _ _ _) <- getBase t = error $ "TODO: reify.Spair: " ++ show n
reify _ (Spair _ _) _ = error "reify.Spair"
reify i (Swtype _ e) (Stype _) = e i
reify _ (Swtype _ _) _ = error "reify.Swtype"
{-
reify i (Siso1 s@SisoData{ sisoLeft = a, sisoRight = b }) (Sid (Stype _) _ _) =
    Iso `App` reifyType i a `App` reifyType i b `App` reify i (sisoLR s) (a `sarr` b) `App`
    reify i (sisoRL s) (b `sarr` a) `App` reifySiso5 i (Siso1 s) `App` reifySiso6 i (Siso1 s)
reify _ (Siso1 _) _ = error "reify.Siso1"
reify _ (Siso n a b c d e f) _ = error $ "TODO: reify.Siso: " ++ show n
-}
reify _ (Szero) t | (n, Snat) <- getBase t = iterate (App Idp) (NatConst 0) `genericIndex` n
reify _ (Szero) _ = error "reify.Szero"
reify i (Ssuc e) t | (n, Snat) <- getBase t = iidp n $ case reify i e Snat of
    NatConst n -> NatConst (n + 1)
    t -> App Suc t
  where iidp n x = iterate (App Idp) x `genericIndex` n
reify _ (Ssuc _) _ = error "reify.Ssuc"
reify i (Spi _ x a b) u@(Stype _) = Pi [([x],reify i a u)] $ reify (i + 1) (b 0 [] $ svar i a) u
reify _ (Spi _ _ _ _) _ = error "reify.Spi"
reify i (Ssigma _ x a b) u@(Stype _) = Sigma [([x],reify i a u)] $ reify (i + 1) (b 0 [] $ svar i a) u
reify _ (Ssigma _ _ _ _) _ = error "reify.Ssigma"
reify i (Sid _ t a b) u@(Stype _) = Id (reify i t u) (reify i a t) (reify i b t)
reify _ (Sid _ _ _ _) _ = error "reify.Sid"
reify _ (Stype u) (Stype _) = Universe u
reify _ (Stype _) _ = error "reify.Stype"
reify _ Snat (Stype _) = Nat
reify _ Snat _ = error "reify.Snat"
reify i (Sidp x) (Sid 0 t _ _) = App Idp (reify i x t)
reify _ (Sidp _) _ = error "reify.Sidp"
reify i (Ne _ e) _ = e i

reifyType :: DBIndex -> Value -> Term
reifyType i t = reify i t (Stype maxBound)

{-
reifySiso5 :: DBIndex -> Value -> Term
reifySiso5 i (Siso _ a b c d e f) = reify i e $ Spi "x" a $ \_ _ v -> Sid b (app 0 d $ app 0 c v) v
reifySiso5 i (Siso1 s) =
    reify i (sisoLI s) $ Spi "x" (sisoLeft s) $ \_ _ v -> Sid (sisoRight s) (app 0 (sisoRL s) $ app 0 (sisoLR s) v) v
reifySiso5 _ _ = error "reifySiso5"

reifySiso6 :: DBIndex -> Value -> Term
reifySiso6 i (Siso _ a b c d e f) = reify i f $ Spi "x" b $ \_ _ v -> Sid a (app 0 c $ app 0 d v) v
reifySiso6 i (Siso1 s) =
    reify i (sisoRI s) $ Spi "x" (sisoRight s) $ \_ _ v -> Sid (sisoLeft s) (app 0 (sisoLR s) $ app 0 (sisoRL s) v) v
reifySiso6 _ _ = error "reifySiso6"
-}
