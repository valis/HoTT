module Value
    ( Value(..), ValueFV
    , D(..), GlobMap
    , svar, sarr, sarrFV, sprod, sprodFV
    , Ctx, CtxV
    , ctxToCtxV
    , cmpTypes, cmpValues
    , reify, reifyType, reifyFV
    , valueFreeVars
    , proj1, proj2, app, coe, pmap, trans
    , idf, idp, action, liftTerm, reduceD, lastD
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
    | Spair Value Value -- Constructor for Sigma-types
    | Spi String [String] Value (Integer -> GlobMap -> Value -> Value) -- Constructor for Type_k
    | Ssigma String [String] Value (Integer -> GlobMap -> Value -> Value) -- Constructor for Type_k
    | Snat | Sid Value Value Value | Stype Level -- Constructors for Type_k
    | Sidp Value -- Constructor for Id
    | Ne [(Term,Term)] Term
    | Swtype Term -- Wrapper for types
    | Siso Integer Value Value Value Value Value Value -- Higher constructor for Type_k
    -- | Scomp Value Value | Ssym Value
type Ctx  = M.Map String (Value,Value)
type CtxV = M.Map String Value
type ValueFV = (Value,[String])

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

infixr 5 `sarrFV`
sarrFV :: Value -> ValueFV -> Value
sarrFV a (b,fv) = Spi "_" fv a $ \k _ _ -> action (genericReplicate k Ud) b

infixr 5 `sarr`
sarr :: Value -> Value -> Value
sarr a b = sarrFV a (b,valueFreeVars b)

sprodFV :: Value -> ValueFV -> Value
sprodFV a (b,fv) = Ssigma "_" fv a $ \k _ _ -> action (genericReplicate k Ud) b

sprod :: Value -> Value -> Value
sprod a b = sprodFV a (b,valueFreeVars b)

ctxToCtxV :: Ctx -> CtxV
ctxToCtxV = M.map fst

cmpTypes :: Value -> Value -> Bool
cmpTypes (Spi x v1 a b) (Spi _ v2 a' b') = cmpTypes a' a && cmpTypes (b 0 [] $ svar fresh a) (b' 0 [] $ svar fresh a')
    where fresh = freshName x (v1 `union` v2)
cmpTypes (Ssigma x v1 a b) (Ssigma _ v2 a' b') = cmpTypes a a' && cmpTypes (b 0 [] $ svar fresh a) (b' 0 [] $ svar fresh a')
    where fresh = freshName x (v1 `union` v2)
cmpTypes (Sid t a b) (Sid t' a' b') = cmpTypes t t' && cmpValues a a' t && cmpValues b b' t
cmpTypes Snat Snat = True
cmpTypes (Stype k) (Stype k') = k <= k'
cmpTypes i@(Siso n a b c d e f) i'@(Siso n' a' b' c' d' e' f') =
    n == n' && cmpTypes a a' && cmpTypes b b' && cmpValues c c' (a `sarr` b) && cmpValues d d' (b `sarr` a)
    && reifySiso5 i == reifySiso5 i' && reifySiso6 i == reifySiso6 i'
cmpTypes (Swtype t) (Swtype t') = t == t'
cmpTypes _ _ = False

cmpValues :: Value -> Value -> Value -> Bool
cmpValues e1 e2 t = reify e1 t == reify e2 t

valueFreeVars :: Value -> [String]
valueFreeVars (Slam _ fv _) = fv
valueFreeVars Szero = []
valueFreeVars (Ssuc e) = valueFreeVars e
valueFreeVars (Spair a b) = valueFreeVars a `union` valueFreeVars b
valueFreeVars (Spi _ fv a _) = fv `union` valueFreeVars a
valueFreeVars (Ssigma _ fv a _) = fv `union` valueFreeVars a
valueFreeVars Snat = []
valueFreeVars (Sid t a b) = valueFreeVars t `union` valueFreeVars a `union` valueFreeVars b
valueFreeVars (Stype _) = []
valueFreeVars (Sidp e) = valueFreeVars e
valueFreeVars (Swtype e) = freeVars e
valueFreeVars (Siso _ a b c d e f) = valueFreeVars a `union` valueFreeVars b `union`
    valueFreeVars c `union` valueFreeVars d `union` valueFreeVars e `union` valueFreeVars f
valueFreeVars (Ne l e) = freeVars e `union` concatMap (\(x,y) -> freeVars x `union` freeVars y) l

idSvar :: Integer -> String -> Value -> Value
idSvar n x t = liftTerm (iterate (App Idp) (Var x) `genericIndex` n) (go n)
  where
    go 0 = t
    go n = Sid (go $ n - 1) (idSvar (n - 1) x t) (idSvar (n - 1) x t)

svar :: String -> Value -> Value
svar x t = idSvar 0 x t

proj1 :: Value -> Value
proj1 (Spair a _) = a
proj1 _ = error "proj1"

proj2 :: Value -> Value
proj2 (Spair _ b) = b
proj2 _ = error "proj1"

app :: Integer -> Value -> Value -> Value
app n (Slam _ _ f) a = f n [] a
app _ _ _ = error "Value.app"

coe :: Value -> Value
coe (Siso _ _ _ f _ _ _) = f
coe _ = error "coe"

pmap :: Integer -> Value -> Value -> Value
pmap n = app (n + 1)

trans :: Integer -> Value -> Value -> Value -> Value
trans n b p = app n (coe $ pmap n (idp b) p)

getBase :: Value -> (Integer,Value)
getBase (Sid t _ _) = let (n,r) = getBase t in (n + 1, r)
getBase r = (0,r)

liftTerm :: Term -> Value -> Value
liftTerm e t | (n,Stype _) <- getBase t = case t of
    Stype _ -> Swtype e
    Sid _ a b -> Siso n a b
        (liftTerm (App (iterate (App Pmap . App Idp) Coe `genericIndex` (n - 1)) e) $ go t n)
        (liftTerm
            (if n == 1
                then App Inv (App Coe e)
                else App (iterate (App Pmap . App Idp) term `genericIndex` (n - 2)) e
            ) $ goRev t n)
        (error "TODO: liftTerm.Siso.1")
        (error "TODO: liftTerm.Siso.2")
    _ -> error "liftTerm.Stype"
  where
    term = App Pmap $ Lam ["x"] $ App Idp $ App Inv $ App Coe (Var "x")
    
    go (Sid _ a b) 1 = a `sarr` b
    go (Sid t p q) n =
        let r = iterate (App Pmap . App Idp) Coe `genericIndex` (n - 2)
            t' = go t (n - 1)
        in Sid t' (liftTerm (App r $ reify p t) t') (liftTerm (App r $ reify q t) t')
    go _ _ = error "liftTerm.go"
    
    goRev (Sid _ a b) 1 = b `sarr` a
    goRev (Sid t p q) 2 =
        let t' = goRev t 1
            a' = App Inv $ App Coe (reify p t)
            b' = App Inv $ App Coe (reify q t)
        in Sid t' (liftTerm a' t') (liftTerm b' t')
    goRev (Sid t p q) n = 
        let r = iterate (App Pmap . App Idp) term `genericIndex` (n - 3)
            t' = goRev t (n - 1)
        in Sid t' (liftTerm (App r $ reify p t) t') (liftTerm (App r $ reify q t) t')
    goRev _ _ = error "liftTerm.goRev"
liftTerm e t | (n, Spi x _ a b) <- getBase t = Slam x (freeVars e) $ \k m v ->
    go a (b 0 [] $ action (genericReplicate k Rd) v) (actionTerm m $ iterate (App Pmap) e `genericIndex` n) k v
  where
    actionTerm :: [D] -> Term -> Term
    actionTerm [] e = e
    actionTerm (Ud:a) e = actionTerm a $ App Pmap (App Idp e)
    actionTerm (_:a) (App Pmap (App Idp e)) = actionTerm a e
    actionTerm _ _ = error "Value.actionTerm"
    
    go a b e' k v = liftTerm (appTerm e' $ reify v $ liftTypeValue k v a) (goType k v)
      where
        liftTypeValue 0 _ a = a
        liftTypeValue k v a = Sid (liftTypeValue (k - 1) (action [Ld] v) a) (action [Ld] v) (action [Rd] v)
        
        appTerm (App Pmap (App Idp e1)) (App Idp e2) = App Idp (appTerm e1 e2)
        appTerm e1 e2 = App e1 e2
        
        goType 0 _ = b
        goType k v = Sid (goType (k - 1) (action [Ld] v)) (go a b e' (k - 1) $ action [Ld] v)
                                                          (go a b e' (k - 1) $ action [Rd] v)
liftTerm e t | (n,Ssigma _ _ a b) <- getBase t = case n of
    0 -> let a' = liftTerm (App Proj1 e) a
         in Spair a' $ liftTerm (App Proj2 e) (b 0 [] a')
    n -> error $ "TODO: liftTerm.Ssigma: " ++ show n
liftTerm (App Idp e) (Sid t _ _) = Sidp (liftTerm e t)
liftTerm (App Idp e) t = error "liftTerm.Idp"
liftTerm e t = Ne (sidToList t) e
  where
    sidToList :: Value -> [(Term,Term)]
    sidToList (Sid t a b) = (reify a t, reify b t) : sidToList t
    sidToList _ = []

idp :: Value -> Value
idp = action [Ud]

idf :: Value
idf = Slam "x" [] $ \_ _ -> id

action :: GlobMap -> Value -> Value
action [] v = v
action m (Slam x fv f) = Slam x fv (\k n -> f k (n ++ m))
action m (Spair e1 e2) = Spair (action m e1) (action m e2) -- TODO: This is incorrect.
action _ Szero = Szero
action _ v@(Ssuc _) = v
action (Ud:m) t@(Spi _ _ _ _) = action m (Siso 1 t t idf idf idf idf)
action (Ud:m) t@(Ssigma _ _ _ _) = action m (Siso 1 t t idf idf idf idf)
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
action (Ld:m) (Ne ((l,_):t) _) = action m (Ne t l)
action (Ld:m) (Ne [] _) = error "action.Ld.Ne"
action (Rd:m) (Ne ((_,r):t) _) = action m (Ne t r)
action (Rd:m) (Ne [] _) = error "action.Rd.Ne"
action (Ud:m) v = action m (Sidp v)
action _ (Spi _ _ _ _) = error "action.Spi"
action _ (Ssigma _ _ _ _) = error "action.Ssigma"
action _ Snat = error "action.Snat"
action _ (Sid _ _ _) = error "action.Sid"
action _ (Stype _) = error "action.Stype"
action _ (Swtype _) = error "action.Swtype"

reifyFV :: ValueFV -> Value -> Term
reifyFV (Slam x _ f, fv) (Spi _ _ a b) =
    let x' = freshName x fv
        v = svar x' a
    in Lam [x'] $ reifyFV (f 0 [] v, x':fv) (b 0 [] v)
reifyFV (Slam _ _ h, fv) (Sid t@(Spi x _ a b) f g) =
    let x' = freshName x fv
        v0 = idSvar 0 x' a
        v1 = idp v0 -- idSvar 1 x' a
    in App (Ext (reify f t) (reify g t)) $ Lam [x'] $ reifyFV (h 1 [] v1, x':fv) $
        Sid (b 0 [] v0) (app 0 f v0) (app 0 g v0)
reifyFV (Slam _ _ h, fv) (Sid t@(Sid t'@(Spi x _ a b) f' g') f g) =
    let x' = freshName x fv
        v0 = idSvar 0 x' a
        v1 = idp v0 -- idSvar 1 x' a
        v2 = idp v1 -- idSvar 2 x' a
    in App (App Pmap $ App Idp (Ext (reify f' t') (reify g' t'))) $
        App (Ext (reify f t) (reify g t)) $ Lam [x'] $ reifyFV (h 2 [] v2, x':fv) $
        Sid (Sid (b 0 [] v0) (app 0 f' v0) (app 0 g' v0)) (app 1 f v1) (app 1 g v1)
reifyFV (Slam _ _ _, _) _ = error "reify.Slam"
reifyFV (Spair e1 e2, _) (Ssigma _ _ a b) = Pair (reify e1 a) (reify e2 $ b 0 [] e1)
reifyFV (Spair e1 e2, _) (Sid t@(Ssigma _ _ a b) p q) = ExtSigma (reify p t) (reify q t) `App`
    Pair (reify e1 $ Sid a (proj1 p) (proj1 q)) (reify e2 $ Sid (b 0 [] $ action [Rd] e1) (action [Ld] e1) (action [Rd] e2))
reifyFV (Spair _ _, _) t | (n, Ssigma _ _ _ _) <- getBase t = error $ "TODO: reify.Spair: " ++ show n
reifyFV (Spair _ _, _) _ = error "reify.Spair"
reifyFV (Swtype e,_) (Stype _) = e
reifyFV (Swtype _,_) _ = error "reify.Swtype"
reifyFV (i@(Siso 1 a b c d _ _), _) (Sid (Stype _) _ _) = Iso `App` reifyType a `App` reifyType b
    `App` reify c (a `sarr` b) `App` reify d (b `sarr` a) `App` reifySiso5 i `App` reifySiso6 i
reifyFV (Siso n a b c d e f, _) _ = error $ "TODO: reify.Siso: " ++ show n
reifyFV (Szero,_) t | (n, Snat) <- getBase t = iterate (App Idp) (NatConst 0) `genericIndex` n
reifyFV (Szero,_) _ = error "reify.Szero"
reifyFV (Ssuc e,fv) t | (n, Snat) <- getBase t = iidp n $ case reifyFV (e,fv) Snat of
    NatConst n -> NatConst (n + 1)
    t -> App Suc t
  where iidp n x = iterate (App Idp) x `genericIndex` n
reifyFV (Ssuc _,_) _ = error "reify.Ssuc"
reifyFV (Spi x _ a b,fv) u@(Stype _) =
    let x' = freshName x fv
    in Pi [([x'],reifyFV (a,valueFreeVars a) u)] $ reifyFV (b 0 [] $ svar x' a, x':fv) u
reifyFV (Spi _ _ _ _, _) _ = error "reify.Spi"
reifyFV (Ssigma x _ a b,fv) u@(Stype _) =
    let x' = freshName x fv
    in Sigma [([x'],reifyFV (a,valueFreeVars a) u)] $ reifyFV (b 0 [] $ svar x' a, x':fv) u
reifyFV (Ssigma _ _ _ _, _) _ = error "reify.Ssigma"
reifyFV (Sid t a b,_) u@(Stype _) =
    Id (reifyFV (t,valueFreeVars t) u) (reifyFV (a,valueFreeVars a) t) $ reifyFV (b,valueFreeVars b) t
reifyFV (Sid _ _ _, _) _ = error "reify.Sid"
reifyFV (Stype u,_) (Stype _) = Universe u
reifyFV (Stype _, _) _ = error "reify.Stype"
reifyFV (Snat,_) (Stype _) = Nat
reifyFV (Snat, _) _ = error "reify.Snat"
reifyFV (Sidp x,fv) (Sid t _ _) = App Idp $ reifyFV (x,fv) t
reifyFV (Sidp _,_) t = error "reify.Sidp"
reifyFV (Ne _ e,_) _ = e

reify :: Value -> Value -> Term
reify v = reifyFV (v, valueFreeVars v)

reifyType :: Value -> Term
reifyType t = reify t (Stype maxBound)

reifySiso5 :: Value -> Term
reifySiso5 (Siso _ a b c d e f) =
    let fv = valueFreeVars b `union` valueFreeVars c `union` valueFreeVars d
    in reify e $ Spi "x" fv a $ \_ _ v -> Sid b (app 0 d $ app 0 c v) v
reifySiso5 _ = error "reifySiso5"

reifySiso6 :: Value -> Term
reifySiso6 (Siso _ a b c d e f) =
    let fv = valueFreeVars a `union` valueFreeVars c `union` valueFreeVars d
    in reify f $ Spi "x" fv b $ \_ _ v -> Sid a (app 0 c $ app 0 d v) v
reifySiso6 _ = error "reifySiso6"
