module TypeChecking
    ( typeOf
    , evalDecl, processDefs
    ) where

import qualified Data.Map as M
import Control.Monad.State
import Data.List

import ErrorDoc
import Value
import Parser.AbsGrammar
import Syntax.Common
import Syntax.Raw
import qualified Syntax.Term as T
import RawToTerm
import Eval

maxType :: Expr -> Expr -> Value -> Value -> EDocM Value
maxType _ _ (Stype k1) (Stype k2) = Right $ Stype (max k1 k2)
maxType e1 e2 t1 t2 = liftErr2 (error "maxType")
    (cmpTypesErr (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr (Stype $ pred maxBound) t2 e2)

processDefs :: [Def] -> [(String,Maybe Expr,[Arg],Expr)]
processDefs [] = []
processDefs (DefType _ t : Def (PIdent (_,name)) args e : defs) = (name,Just t,args,e) : processDefs defs
processDefs (Def (PIdent (_,name)) args e : defs) = (name,Nothing,args,e) : processDefs defs
processDefs _ = error "processDefs"

typeOf'depType :: Ctx -> [TypedVar] -> Expr -> EDocM Value
typeOf'depType ctx [] e = typeOf ctx e
typeOf'depType ctx (TypedVar _ vars t : list) e = do
    tv <- typeOf ctx t
    let e' = Pi list e
    cmpTypesErr (Stype $ pred maxBound) tv t
    ctx' <- updateCtx ctx (evalRaw ctx t (Just tv)) vars
    ev <- typeOf ctx' e'
    maxType t e' tv ev
  where
    updateCtx ctx _ (Var (NoArg _)) = Right ctx
    updateCtx ctx tv (Var (Arg (PIdent (_,x)))) = Right (M.insert x (svar x tv,tv) ctx)
    updateCtx ctx tv (App a (Var (NoArg _))) = updateCtx ctx tv a
    updateCtx ctx tv (App a (Var (Arg (PIdent (_,x))))) = fmap (M.insert x (svar x tv,tv)) (updateCtx ctx tv a)
    updateCtx _ _ e = Left [emsgLC (getPos e) "Expected identifier" enull]

dropParens :: Expr -> Expr
dropParens (Paren _ e) = dropParens e
dropParens e = e

data H = P Expr Value Value Value | T Value | N

typeOf :: Ctx -> Expr -> EDocM Value
typeOf ctx e = typeOfH ctx e N

typeOfH :: Ctx -> Expr -> H -> EDocM Value
typeOfH ctx (Let defs e) h = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    typeOfH ctx' e h
typeOfH ctx (Paren _ e) h = typeOfH ctx e h
typeOfH ctx (Lam _ [] e) h = typeOfH ctx e h

typeOfH ctx e1@(Lam (PLam (lc,_)) (x:xs) e) (P _ ty a b) = do
    let p = if null xs then getPos e else binderGetPos (head xs)
        e' = Lam (PLam (p,"\\")) xs e
        (x',e'') = renameExpr (freeVars e') (unBinder x) e'
    s <- typeOf (M.insert x' (svar x' ty,ty) ctx) e''
    if elem x' $ T.freeVars (reifyType s)
        then inferErrorMsg lc "lambda expression"
        else let v1 = evalRaw ctx e1 $ Just (ty `sarr` s)
             in Right $ Sid s (app 0 v1 a) (app 0 v1 b)
typeOfH ctx e1 (P e2 act a b) = do
    t1 <- typeOf ctx e1
    let v1 = evalRaw ctx e1 Nothing
    typeOfPmap ctx t1 v1 v1 (Sid act a b) e1 e2

typeOfH ctx (Lam _ (x:xs) e) (T r@(Spi z fv a b)) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        (x',e') = renameExpr fv (unBinder x) (Lam (PLam (p,"\\")) xs e)
        v = svar x' a
    in typeOfH (M.insert x' (v,a) ctx) e' (T (b 0 [] v)) >> return r
typeOfH _ (Lam _ (Binder arg : _) _) (T ty) =
    let lc = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    in Left [emsgLC lc "" $ expType 1 ty $$ etext "But lambda expression has pi type"]
typeOfH _ i@(Idp _) (T exp@(Spi x _ a _)) = do
    let ctx = M.singleton (freshName "a" [x]) a
    cmpTypesErr exp (eval 0 ctx $ T.Pi [([x],T.Var "a")] $ T.Id (T.Var "a") (T.Var x) (T.Var x)) i
    return exp
typeOfH _ (Idp (PIdp (lc,_))) (T ty) =
    Left [emsgLC lc "" $ expType 1 ty $$ etext "But idp has pi type"]
typeOfH ctx e@(Coe (PCoe (lc,_))) (T ty@(Spi v fv a@(Sid (Stype _) x y) b)) = case b 0 [] $ svar (freshName v fv) a of
    Spi v' fv' x' y' -> if cmpTypes x x' && cmpTypes y (y' 0 [] $ svar (freshName v' fv') x')
        then return ty
        else coeErrorMsg lc ty
    _ -> coeErrorMsg lc ty
typeOfH ctx (Coe (PCoe (lc,_))) (T ty) = coeErrorMsg lc ty
typeOfH ctx ea@(App e1 e) (T exp@(Sid t a b)) | Idp _ <- dropParens e1 = do
    typeOfH ctx e (T t)
    let e' = evalRaw ctx e (Just t)
    cmpTypesErr exp (Sid t e' e') ea
    return exp
typeOfH ctx (App e1 _) (T exp) | Idp (PIdp (lc,_)) <- dropParens e1 =
    Left [emsgLC lc "" $ expType 1 exp $$ etext "But idp _ has Id type"]
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfH ctx e@(Pmap (Ppmap (lc,_))) (T exp@(Spi v fv a@(Sid (Spi v' fv' a' b') f g) b)) =
    case isArr v fv a b of
        Just (Spi v2 fv2 a2'@(Sid a2 x y) b2') | cmpTypes a2 a' ->
            let ctx' = [("a",a),("a'",a'),("x",x),("y",y),("B",Slam v' fv' b'),("f'",app 0 f x),("g'",app 0 g y)]
                term = T.Pi [([],T.Var "a")] $ T.Pi [(["p"],T.Id (T.Var "a'") (T.Var "x") (T.Var "y"))] $
                    T.Id (T.Var "B" `T.App` T.Var "y")
                         (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.Var "p") `T.App` T.Var "f'")
                         (T.Var "g'")
            in cmpTypesErr exp (eval 0 (M.fromList ctx') term) e >> return exp
        _ -> pmapErrorMsg lc exp
typeOfH ctx (Pmap (Ppmap (lc,_))) (T exp) = pmapErrorMsg lc exp
typeOfH ctx ea@(App e1 e) (T ty@(Spi v fv a'@(Sid a x y) b')) | Pmap _ <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid (Spi v1 fv1 a1 b1) f g | cmpTypes a a1 ->
            let ctx' = [("a'",a'),("B",Slam v1 fv1 b1),("y",y),("f'",app 0 f x),("g'",app 0 g y)]
                term = T.Pi [(["p"],T.Var "a'")] $ T.Id (T.Var "B" `T.App` T.Var "y")
                    (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.Var "p") `T.App` T.Var "f'")
                    (T.Var "g'")
            in cmpTypesErr ty (eval 0 (M.fromList ctx') term) ea >> return ty
        _ -> Left [emsgLC (getPos e) "" $ etext "Expected type: Id(" <+> epretty (T.Pi [([],reifyType a)] $ T.Var "_")
                <+> etext ") _ _" $$ etext "But term" <+> epretty e <+> etext "has type" <+> epretty (reifyType t)]
typeOfH ctx (App e1 e) (T ty) | Pmap (Ppmap (lc,_)) <- dropParens e1 = pmap1ErrorMsg lc ty
typeOfH ctx (Ext (PExt (lc,_))) (T ty@(Spi x' fv' s@(Spi _ _ a' b') t)) = case isArr x' fv' s t of
    Just (Sid (Spi x fv a b) f g) | cmpTypes a a' ->
        let v = svar (freshName x $ fv `union` fv' `union` valueFreeVars f `union` valueFreeVars g) a
        in if cmpTypes (b' 0 [] v) (Sid (b 0 [] v) (app 0 f v) (app 0 g v)) then Right ty else extErrorMsg lc ty
    _ -> extErrorMsg lc ty
-- ext : (s : Id A x x') * Id (B x') (trans B s y) y' -> Id ((x : A) * B x) (x,y) (x',y')
--       a'              * b'                         -> Id (a       * b  ) p     q
typeOfH ctx (Ext (PExt (lc,_))) (T ty@(Spi x' fv' s@(Ssigma _ _ a' b') t)) = case isArr x' fv' s t of
    Just (Sid (Ssigma x fv a b) p q) ->
        let fva = fv `union` fv' `union` valueFreeVars p `union` valueFreeVars q
            v = svar (freshName x fva) $ Sid a (proj1 p) (proj1 q)
        in if cmpTypes a' (Sid a (proj1 p) (proj1 q)) &&
              cmpTypes (b' 0 [] v) (Sid (b 0 [] $ proj1 q) (trans 0 (Slam x fv b) s $ proj2 p) (proj2 q))
           then Right ty
           else extErrorMsg lc ty
    _ -> extErrorMsg lc ty
typeOfH ctx (Ext (PExt (lc,_))) (T ty) = extErrorMsg lc ty
typeOfH ctx (App e1 e) (T r@(Sid (Spi x fv a b) f g)) | Ext _ <- dropParens e1 = do
    let fv' = fv `union` valueFreeVars f `union` valueFreeVars g
    typeOfH ctx e $ T $ Spi x fv' a $ \k m v -> Sid (b k m v) (app k (action m f) v) (app k (action m g) v)
    return r
-- (s : Id a (proj1 p) (proj1 q)) * (Id (B (proj1 q)) (trans B s (proj2 p)) (proj2 q))
typeOfH ctx (App e1 e) (T r@(Sid (Ssigma x fv a b) p q)) | Ext _ <- dropParens e1 = do
    let fv' = fv `union` valueFreeVars p `union` valueFreeVars q
    typeOfH ctx e $ T $ Ssigma x fv' (Sid a (proj1 p) (proj1 q)) $ \k m s ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x fv b) s $ action m (proj2 p)
            r3 = action m (proj2 q)
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)]) $ T.Id (T.Var "r1") (T.Var "r2") (T.Var "r3")
    return r
typeOfH ctx (App e1 e) (T exp) | Ext (PExt (lc,_)) <- dropParens e1 = Left [emsgLC lc "" $ expType (-1) exp
    $$ etext "But term ext _ has type either of the form Id ((x : A) -> B x) _ _ or of the form Id ((x : A) * B x) _ _"]
typeOfH ctx (Pair e1 e2) (T r@(Ssigma _ _ a b)) = do
    typeOfH ctx e1 (T a)
    typeOfH ctx e2 $ T $ b 0 [] $ evalRaw ctx e1 (Just a)
    return r
typeOfH ctx e@(Pair _ _) (T exp) =
    Left [emsgLC (getPos e) "" $ expType (-1) exp $$ etext "But term" <+> epretty e <+> etext "has Sigma type"]
typeOfH ctx (Proj1 (PProjl (lc,_))) (T r@(Spi x fv a'@(Ssigma _ _ a _) b)) = case isArr x fv a' b of
    Just b' | cmpTypes a b' -> Right r
    _ -> proj1ErrorMsg lc r
typeOfH ctx (Proj1 (PProjl (lc,_))) (T exp) = proj1ErrorMsg lc exp
-- proj2 : (p : (x : A) -> B x) -> B (proj1 p)
typeOfH ctx (Proj2 (PProjr (lc,_))) (T r@(Spi x fv a'@(Ssigma _ _ a b) b')) =
    let x' = freshName x fv
    in if cmpTypes (b 0 [] $ liftTerm (T.App T.Proj1 $ T.Var x') a) (b' 0 [] $ svar x' a')
        then Right r
        else proj2ErrorMsg lc r
typeOfH ctx (Proj2 (PProjr (lc,_))) (T exp) = proj2ErrorMsg lc exp
typeOfH ctx (Comp _) (T exp@(Spi v1 fv1 a1@(Sid t1 x1 y1) b1))
    | Just (Spi v2 fv2 a2@(Sid t2 x2 y2) b2) <- isArr v1 fv1 a1 b1, Just (Sid t3 x3 y3) <- isArr v2 fv2 a2 b2
    , cmpTypes t1 t2 && cmpTypes t2 t3 && cmpValues y1 x2 t1 && cmpValues x1 x3 t1 && cmpValues y2 y3 t2 = Right exp
typeOfH ctx (Comp (PComp (lc,_))) (T exp) = Left [emsgLC lc "" $ expType (-1) exp $$
    etext "But comp has type of the form Id A x y -> Id A y z -> Id A x z"]
typeOfH ctx (Inv _) (T exp@(Spi v fv a@(Sid t x y) b))
    | Just (Sid t' x' y') <- isArr v fv a b, cmpTypes t t' && cmpValues x y' t && cmpValues x' y t = Right exp
typeOfH ctx (Inv (PInv (lc,_))) (T exp) = Left [emsgLC lc "" $ expType (-1) exp $$
    etext "But inv has type of the form Id A x y -> Id A y x"]
typeOfH ctx e (T exp) = do
    act <- typeOf ctx e
    cmpTypesErr exp act e
    return exp

typeOfH ctx (Pair e1 e2) N = liftErr2' sprod (typeOf ctx e1) (typeOf ctx e2)
typeOfH _ (Lam (PLam (lc,_)) _ _) N = inferErrorMsg lc "the argument"
typeOfH _ (Idp (PIdp (lc,_))) N = inferErrorMsg lc "idp"
typeOfH _ (Coe (PCoe (lc,_))) N = inferErrorMsg lc "coe"
typeOfH ctx (App e1 e) N | Idp _ <- dropParens e1 = do
    t <- typeOf ctx e
    let v = evalRaw ctx e (Just t)
    Right (Sid t v v)
typeOfH _ (Pmap (Ppmap (lc,_))) N = inferErrorMsg lc "pmap"
typeOfH ctx (Ext (PExt (lc,_))) N = inferErrorMsg lc "ext"
typeOfH _ (Proj1 (PProjl (lc,_))) N = inferErrorMsg lc "proj1"
typeOfH _ (Proj2 (PProjr (lc,_))) N = inferErrorMsg lc "proj2"
typeOfH ctx (App e1 e) N | Proj1 _ <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Ssigma _ _ a _ -> Right a
        _ -> expTypeBut "Sigma" e t
typeOfH ctx (App e1 e) N | Proj2 (PProjr p) <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Ssigma _ _ a b -> Right $ b 0 [] $ evalRaw ctx (App (Proj1 $ PProjl p) e) (Just a)
        _ -> expTypeBut "Sigma" e t
typeOfH _ (App e1 _) N | Pmap (Ppmap (lc,_)) <- dropParens e1 = inferErrorMsg lc "ext"
-- pmap (idp e1) e2
typeOfH ctx (App e1' e2) N
    | App e3 e4 <- dropParens e1'
    , Pmap _ <- dropParens e3
    , App e5 e1 <- dropParens e4
    , Idp _ <- dropParens e5 = do
        t2 <- typeOf ctx e2
        case t2 of
            Sid s a b -> typeOfH ctx e1 (P e2 s a b)
            _ -> expTypeBut "Id" e2 t2
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfH ctx (App e1' e2) N | App e3 e1 <- dropParens e1', Pmap _ <- dropParens e3 = do
    (t1,t2) <- liftErr2' (,) (typeOf ctx e1) (typeOf ctx e2)
    case t1 of
        Sid t f g -> typeOfPmap ctx t f g t2 e1 e2
        _ -> expTypeBut "Id" e1 t1
typeOfH ctx (App e1 e) N | Coe _ <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid (Stype _) x y -> Right (x `sarr` y)
        _ -> expTypeBut "Id Type _ _" e t
typeOfH ctx (App e1 e) N | Inv _ <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid t' x y -> Right (Sid t' y x)
        _ -> expTypeBut "Id" e t
typeOfH ctx (App e1' e2) N | App e3 e1 <- dropParens e1', Comp (PComp (lc,_)) <- dropParens e3 = do
    r <- liftErr2' (,) (typeOf ctx e1) (typeOf ctx e2)
    case r of
        (Sid t1 x1 y1, Sid t2 x2 y2) | cmpTypes t1 t2 -> if cmpValues y1 x2 t1
            then Right (Sid t1 x1 y2)
            else Left [emsgLC lc "" $ etext "Terms" <+> epretty (reify y1 t1)
                <+> etext "and" <+> epretty (reify x2 t2) <+> etext "must be equal"]
        (Sid t1 _ _, Sid t2 _ _) -> Left [emsgLC lc "" $ etext "Types" <+> epretty (reifyType t1)
                <+> etext "and" <+> epretty (reifyType t2) <+> etext "must be equal"]
        (Sid _ _ _, t2) -> expTypeBut "Id" e2 t2
        (t1, Sid _ _ _) -> expTypeBut "Id" e1 t1
        (t1, t2) -> liftErr2' const (expTypeBut "Id" e1 t1) (expTypeBut "Id" e2 t2)
typeOfH ctx (Arr e1 e2) N = liftErr2 (maxType e1 e2) (typeOf ctx e1) (typeOf ctx e2)
typeOfH ctx (Prod e1 e2) N = typeOf ctx (Arr e1 e2)
typeOfH ctx (Pi tv e) N = typeOf'depType ctx tv e
typeOfH ctx (Sigma tv e) N = typeOf'depType ctx tv e
typeOfH ctx (Id a b) N = do
    a' <- typeOf ctx a
    typeOfH ctx b (T a')
    return $ typeOfTerm ctx (reifyType a')
typeOfH _ (Nat _) N = Right $ Stype (Finite 0)
typeOfH _ (Universe (U (_,t))) N = Right $ Stype $ succ (parseLevel t)
typeOfH ctx (App e1 e2) N = do
    t1 <- typeOf ctx e1
    case t1 of
        Spi _ _ a b -> do
            typeOfH ctx e2 (T a)
            return $ b 0 [] $ evalRaw ctx e2 (Just a)
        _ -> expTypeBut "pi" e1 t1
typeOfH _ (Var (NoArg (Pus (lc,_)))) N = Left [emsgLC lc "Expected identifier" enull]
typeOfH ctx (Var (Arg (PIdent (lc,x)))) N = case M.lookup x ctx of
    Nothing -> Left [emsgLC lc ("Unknown identifier " ++ x) enull]
    Just (_,t) -> Right t
typeOfH _ (Suc _) N = Right (sarr Snat Snat)
typeOfH _ (NatConst _) N = Right Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfH _ (Rec _) N = Right $ eval 0 M.empty $ T.Pi [(["P"], T.Pi [([],T.Nat)] $ T.Universe Omega)] $
    T.Pi [([], T.App (T.Var "P") $ T.NatConst 0)] $ T.Pi [([], iht)] $ T.Pi [(["x"],T.Nat)] $ T.App (T.Var "P") (T.Var "x")
  where iht = T.Pi [(["x"],T.Nat)] $ T.Pi [([], T.App (T.Var "P") (T.Var "x"))] $ T.App (T.Var "P") $ T.App T.Suc (T.Var "x")
typeOfH ctx (Typed e t) N = do
    typeOfH ctx t $ T (Stype maxBound)
    typeOfH ctx e $ T $ evalRaw ctx t $ Just (Stype maxBound)
typeOfH ctx (Iso _) N =
    let term = T.Pi [(["A"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [(["B"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [([],T.Pi [([],T.Var "A")] $ T.Var "B")] $
               T.Pi [([],T.Pi [([],T.Var "B")] $ T.Var "A")] $
               T.Id (T.Universe $ pred $ pred maxBound) (T.Var "A") (T.Var "B")
    in Right (eval 0 M.empty term)
typeOfH ctx (Comp (PComp (lc,_))) N = inferErrorMsg lc "comp"
typeOfH ctx (Inv (PInv (lc,_))) N = inferErrorMsg lc "inv"

typeOfPmap :: Ctx -> Value -> Value -> Value -> Value -> Expr -> Expr -> EDocM Value
typeOfPmap ctx (Spi v fv a b) f g (Sid a' x y) _ e2
    | cmpTypes a' a = Right $ Sid (b 0 [] y) (trans 0 (Slam v fv b) (evalRaw ctx e2 Nothing) (app 0 f x)) (app 0 g y)
    | otherwise = pmapErrMsg e2 a' (eprettyType a)
typeOfPmap _ t1 _ _ (Sid _ _ _) e1 _ = pmapErrMsg e1 t1 (etext "_ -> _")
typeOfPmap _ _ _ _ t2 _ e2 = expTypeBut "Id" e2 t2

pmapErrMsg :: Expr -> Value -> EDoc -> EDocM a
pmapErrMsg expr ty i =
    Left [emsgLC (getPos expr) "" $ etext "Expected type of the form Id(" <> i <> etext ") _ _" $$
        etext "But term" <+> epretty expr <+> etext "has type Id(" <> eprettyType ty <> etext ") _ _"]

isArr :: String -> [String] -> Value -> (Integer -> [D] -> Value -> Value) -> Maybe Value
isArr x fv t f =
    let x' = freshName x fv
        r = f 0 [] (svar x' t)
    in if elem x' (valueFreeVars r) then Nothing else Just r

evalDecl :: String -> Expr -> Maybe Expr -> StateT Ctx EDocM (Value,Value)
evalDecl name expr mty = do
    ctx <- get
    tv <- case mty of
        Nothing -> lift (typeOf ctx expr)
        Just ty -> do
            lift $ typeOfH ctx ty $ T $ Stype (pred maxBound)
            let tv = evalRaw ctx ty $ Just $ Stype (pred maxBound)
            lift $ typeOfH ctx expr (T tv)
            return tv
    let ev = evalRaw ctx expr (Just tv)
    put (M.insert name (ev,tv) ctx)
    return (ev,tv)

eprettyType :: Value -> EDoc
eprettyType t = epretty $ T.simplify (reifyType t)

inferErrorMsg :: (Int,Int) -> String -> EDocM a
inferErrorMsg lc s = Left [emsgLC lc ("Cannot infer type of " ++ s) enull]

coeErrorMsg :: (Int,Int) -> Value -> EDocM a
coeErrorMsg lc ty = Left [emsgLC lc "" $ expType 1 ty $$ etext "But coe has type of the form Id Type A B -> A -> B"]

pmapErrorMsg :: (Int,Int) -> Value -> EDocM a
pmapErrorMsg lc ty = Left [emsgLC lc "" $ expType (-1) ty $$ etext ("But pmap has type of the form "
    ++ "Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)")]

pmap1ErrorMsg :: (Int,Int) -> Value -> EDocM a
pmap1ErrorMsg lc ty = Left [emsgLC lc "" $ expType (-1) ty $$
    etext "But pmap _ has type of the form (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)"]

proj1ErrorMsg :: (Int,Int) -> Value -> EDocM a
proj1ErrorMsg lc exp = Left [emsgLC lc "" $ expType (-1) exp $$
    etext "But proj1 has type of the form ((a : A) -> B a) -> A"]

proj2ErrorMsg :: (Int,Int) -> Value -> EDocM a
proj2ErrorMsg lc exp = Left [emsgLC lc "" $ expType (-1) exp $$
    etext "But proj2 has type of the form (p : (a : A) -> B a) -> B (proj1 p)"]

extErrorMsg :: (Int,Int) -> Value -> EDocM a
extErrorMsg lc exp = Left [emsgLC lc "" $ expType (-1) exp
    $$ etext ("But ext has type either of the form ((x : A) -> f x = g x) -> f = g or "
    ++ "of the form (s : Id A a a') * Id (B a') (trans B s b) b' -> Id ((a : A) * B a) (a,b) (a',b')")]

expType :: Int -> Value -> EDoc
expType l ty = etext "Expected type:" <+> eprettyLevel l (T.simplify $ reifyType ty)

cmpTypesErr :: Value -> Value -> Expr -> EDocM ()
cmpTypesErr t1 t2 e = if cmpTypes t2 t1
    then Right ()
    else Left [emsgLC (getPos e) "" $ expType (-1) t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> eprettyType t2]

expTypeBut :: String -> Expr -> Value -> EDocM a
expTypeBut exp e act = Left [emsgLC (getPos e) "" $ etext ("Expected " ++ exp ++ " type") $$
    etext "But term" <+> epretty e <+> etext "has type" <+> eprettyHead (T.simplify $ reifyType act)]
