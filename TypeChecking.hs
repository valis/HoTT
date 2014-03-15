module TypeChecking
    ( typeOf, hasType
    , evalDecl, processDefs
    ) where

import qualified Data.Map as M
import Control.Monad.State

import ErrorDoc
import Value
import Parser.AbsGrammar
import Syntax.Common
import Syntax.Raw
import qualified Syntax.Term as T
import RawToTerm

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
    updateCtx _ _ e = let (l,c) = getPos e in Left [emsgLC l c "Expected identifier" enull]

dropParens :: Expr -> Expr
dropParens (Paren _ e) = dropParens e
dropParens e = e

typeOf :: Ctx -> Expr -> EDocM Value
typeOf ctx (Lam _ [] e) = typeOf ctx e
typeOf _ (Lam (PLam (lc,_)) _ _) = inferErrorMsg lc "the argument"
typeOf _ (Idp (PIdp (lc,_))) = inferErrorMsg lc "idp"
typeOf _ (Trans (PTrans (lc,_))) = inferErrorMsg lc "trans"
typeOf ctx (Let defs e) = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    typeOf ctx' e
typeOf ctx (App e1 e) | Idp _ <- dropParens e1 = do
    t <- typeOf ctx e
    let v = evalRaw ctx e (Just t)
    Right (Sid t v v)
typeOf _ (Ext (PExt (lc,_))) = inferErrorMsg lc "ext"
typeOf _ (App e1 _) | Ext (PExt (lc,_)) <- dropParens e1 = inferErrorMsg lc "ext"
typeOf ctx (App e1' e2)
    | App e3 e4 <- dropParens e1'
    , Ext _ <- dropParens e3
    , App e5 e1 <- dropParens e4
    , Idp _ <- dropParens e5 = do
        t2 <- typeOf ctx e2
        case t2 of
            Sid s a b -> do
                t <- typeOfLam (getPos e2) ctx e1 e2 t2
                let e' = app 0 $ evalRaw ctx e1 (Just $ s `sarr` t)
                Right $ Sid t (e' a) (e' b)
            _ -> expTypeBut "Id" e2 t2
typeOf ctx (App e1' e2) | App e3 e1 <- dropParens e1', Ext _ <- dropParens e3 = do
    r <- liftErr2' (,) (typeOf ctx e1) (typeOf ctx e2)
    case r of
        (Sid (Spi v fv a b') f g, Sid t x y) | Just b <- isArr v fv a b' -> if cmpTypes t a
            then Right $ Sid b (app 0 f x) (app 0 g y)
            else let (l,c) = getPos e2
                 in Left [emsgLC l c "" $ etext "Expected type of the form Id("
                    <> epretty (T.simplify $ reify a $ Stype maxBound) <> etext ") _ _"
                    $$ etext "But term" <+> epretty e2 <+> etext "has type Id("
                    <> epretty (T.simplify $ reify t $ Stype maxBound) <> etext ") _ _"]
        (Sid t1 _ _, Sid _ _ _) ->
            let (l,c) = getPos e1
            in Left [emsgLC l c "" $ etext "Expected type of the form Id(_ -> _) _ _"
                    $$ etext "But term" <+> epretty e1 <+> etext "has type Id("
                    <> epretty (T.simplify $ reify t1 $ Stype maxBound) <> etext ") _ _"]
        (t1, Sid _ _ _) -> expTypeBut "Id" e1 t1
        (_, t2) -> expTypeBut "Id" e2 t2
typeOf ctx (App e1 e) | Trans _ <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid (Stype _) x y -> Right (x `sarr` y)
        _ -> expTypeBut "Id Type _ _" e t
typeOf ctx (Arr e1 e2) =
    liftErr2 (maxType e1 e2) (typeOf ctx e1) (typeOf ctx e2)
typeOf ctx (Prod e1 e2) = typeOf ctx (Arr e1 e2)
typeOf ctx (Pi tv e) = typeOf'depType ctx tv e
typeOf ctx (Sigma tv e) = typeOf'depType ctx tv e
typeOf ctx (Id a b) = do
    a' <- typeOf ctx a
    hasType ctx b a'
    return $ typeOfTerm ctx $ reify a' (Stype maxBound)
typeOf _ (Nat _) = Right $ Stype (Finite 0)
typeOf _ (Universe (U (_,t))) = Right $ Stype $ succ (parseLevel t)
typeOf ctx (App e1 e2) = do
    t1 <- typeOf ctx e1
    case t1 of
        Spi _ _ a b -> do
            hasType ctx e2 a
            return $ b $ evalRaw ctx e2 (Just a)
        _ -> expTypeBut "pi" e1 t1
typeOf _ (Var (NoArg (Pus ((l,c),_)))) = Left [emsgLC l c "Expected identifier" enull]
typeOf ctx (Var (Arg (PIdent ((l,c),x)))) = case M.lookup x ctx of
    Nothing -> Left [emsgLC l c ("Unknown identifier " ++ x) enull]
    Just (_,t) -> Right t
typeOf _ (Suc _) = Right (sarr Snat Snat)
typeOf _ (NatConst _) = Right Snat
typeOf _ (Rec _) = Right $ Spi "P" [] (Snat `sarr` Stype maxBound) $ \p ->
    let pfv = valueFreeVars p
    in app 0 p Szero `sarr` (Spi "x" pfv Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" pfv Snat (app 0 p)
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOf ctx (Paren _ e) = typeOf ctx e

isArr :: String -> [String] -> Value -> (Value -> Value) -> Maybe Value
isArr x fv t f =
    let x' = freshName x fv
        r = f (svar x' t)
    in if elem x' (valueFreeVars r) then Nothing else Just r

typeOfLam :: (Int,Int) -> Ctx -> Expr -> Expr -> Value -> EDocM Value
typeOfLam lc' ctx (Lam _ [] e) e2 ty = typeOfLam lc' ctx e e2 ty
typeOfLam _ ctx (Lam (PLam ((l,c),_)) (x:xs) e) _ (Sid ty _ _) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        x' = unBinder x
    in do
        s <- typeOf (M.insert x' (svar x' ty,ty) ctx) $ Lam (PLam (p,"\\")) xs e
        if elem x' $ T.freeVars $ reify s (Stype maxBound)
            then Left [emsgLC l c "Cannot infer type of lambda expression" enull]
            else Right s
typeOfLam lc' ctx (Paren _ e) e2 act = typeOfLam lc' ctx e e2 act
typeOfLam (l',c') ctx e e2 (Sid act _ _) = do
    t <- typeOf ctx e
    case t of
        Spi x fv exp r -> if cmpTypes act exp
            then case isArr x fv exp r of
                Just r' -> Right r'
                Nothing -> expTypeBut "arrow" e t
            else let em s t = s <> etext "(" <> epretty (T.simplify $ reify t $ Stype maxBound) <> etext ") _ _"
                 in Left [emsgLC l' c' "" $ em (etext "Expected type: Id") exp $$
                    em (etext "But term" <+> epretty e2 <+> etext "has type Id") act]
        _ -> expTypeBut "pi" e t
typeOfLam _ _ _ _ _ = error "typeOfLam"

hasType :: Ctx -> Expr -> Value -> EDocM ()
hasType ctx (Lam _ [] e) ty = hasType ctx e ty
hasType ctx (Lam i (x:xs) e) (Spi z fv a b) =
    let (x',e') = renameExpr fv (unBinder x) (Lam i xs e)
        v = svar x' a
    in hasType (M.insert x' (v,a) ctx) e' (b v)
hasType _ (Lam _ (Binder arg : _) _) ty =
    let (l,c) = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    in Left [emsgLC l c "" $ expType 1 ty $$ etext "But lambda expression has pi type"]
hasType _ i@(Idp _) exp@(Spi x _ a _) =
    cmpTypesErr exp (Spi x (valueFreeVars a) a $ \v -> Sid a v v) i
hasType _ (Idp (PIdp ((l,c),_))) ty =
    Left [emsgLC l c "" $ expType 1 ty $$ etext "But idp has pi type"]
hasType ctx (Paren _ e) ty = hasType ctx e ty
hasType ctx (Let defs e) ty = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    hasType ctx' e ty
hasType ctx e@(Trans (PTrans (lc,_))) ty@(Spi v fv a@(Sid (Stype _) x y) b) = case b $ svar (freshName v fv) a of
    Spi v' fv' x' y' -> if cmpTypes x x' && cmpTypes y (y' $ svar (freshName v' fv') x')
        then Right ()
        else transErrorMsg lc ty
    _ -> transErrorMsg lc ty
hasType ctx (Trans (PTrans (lc,_))) ty = transErrorMsg lc ty
hasType ctx ea@(App e1 e) exp@(Sid t a b) | Idp _ <- dropParens e1 = do
    hasType ctx e t
    let e' = evalRaw ctx e (Just t)
    cmpTypesErr exp (Sid t e' e') ea
hasType ctx (App e1 _) exp | Idp (PIdp ((l,c),_)) <- dropParens e1 =
    Left [emsgLC l c "" $ expType 1 exp $$ etext "But idp _ has Id type"]
-- ext :: Id (A -> B) f g -> Id A x y -> Id B (f x) (g y)
hasType ctx (Ext (PExt (lc,_))) exp@(Spi v fv a@(Sid (Spi v' fv' a' b') f g) b) =
    case (isArr v fv a b, isArr v' fv' a' b') of
        (Just (Spi v2 fv2 a2'@(Sid a2 x y) b2'), Just t) | Just (Sid b2 x' y') <- isArr v2 fv2 a2' b2', cmpTypes a2 a'
            && cmpTypes t b2 && reify x' b2 == reify (app 0 f x) t && reify y' b2 == reify (app 0 g y) t -> Right ()
        _ -> extErrorMsg lc exp
hasType ctx (Ext (PExt (lc,_))) exp = extErrorMsg lc exp
hasType ctx ea@(App e1 e) ty@(Spi v fv a'@(Sid a x y) b') | Ext (PExt ((l,c),_)) <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid (Spi v1 fv1 a1 b1') f g | Just b1 <- isArr v1 fv1 a1 b1' -> if cmpTypes a a1
            then cmpTypesErr ty (a' `sarr` Sid b1 (app 0 f x) (app 0 g y)) ea
            else Left [emsgLC l c "" $ expType (-1) ty $$ etext "But term" <+> epretty ea <+>
                 etext "has type of the form Id" <+> epretty (reify a1 $ Stype maxBound) <+> etext "_ _ -> Id _ _ _"]
        _ -> ext1ErrorMsg (l,c) ty
hasType ctx (App e1 e) ty | Ext (PExt (lc,_)) <- dropParens e1 = ext1ErrorMsg lc ty
hasType ctx e exp = do
    act <- typeOf ctx e
    cmpTypesErr exp act e

inferErrorMsg :: (Int,Int) -> String -> EDocM a
inferErrorMsg (l,c) s = Left [emsgLC l c ("Cannot infer type of " ++ s) enull]

transErrorMsg :: (Int,Int) -> Value -> EDocM a
transErrorMsg (l,c) ty =
    Left [emsgLC l c "" $ expType 1 ty $$ etext "But trans has type of the form Id Type A B -> A -> B"]

ext1ErrorMsg :: (Int,Int) -> Value -> EDocM a
ext1ErrorMsg (l,c) ty = Left [emsgLC l c "" $ expType (-1) ty $$ etext "But ext _ has type of the form x = y -> _ x = _ y"]

extErrorMsg :: (Int,Int) -> Value -> EDocM a
extErrorMsg (l,c) ty =
    Left [emsgLC l c "" $ expType (-1) ty $$ etext "But ext has type of the form Id (A -> B) f g -> a = a' -> f a = g a'"]

evalDecl :: String -> Expr -> Maybe Expr -> StateT Ctx EDocM (Value,Value)
evalDecl name expr mty = do
    ctx <- get
    tv <- case mty of
        Nothing -> lift (typeOf ctx expr)
        Just ty -> do
            lift $ hasType ctx ty $ Stype (pred maxBound)
            let tv = evalRaw ctx ty $ Just $ Stype (pred maxBound)
            lift (hasType ctx expr tv)
            return tv
    let ev = evalRaw ctx expr (Just tv)
    put (M.insert name (ev,tv) ctx)
    return (ev,tv)

expType :: Int -> Value -> EDoc
expType l ty = etext "Expected type:" <+> eprettyLevel l (T.simplify $ reify ty $ Stype maxBound)

cmpTypesErr :: Value -> Value -> Expr -> EDocM ()
cmpTypesErr t1 t2 e = if cmpTypes t2 t1
    then Right ()
    else let (l,c) = getPos e in Left [emsgLC l c "" $ expType (-1) t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> epretty (T.simplify $ reify t2 $ Stype maxBound)]

expTypeBut :: String -> Expr -> Value -> EDocM a
expTypeBut exp e act =
    let (l,c) = getPos e
    in Left [emsgLC l c "" $ etext ("Expected " ++ exp ++ " type") $$
            etext "But term" <+> epretty e <+> etext "has type" <+> eprettyHead (T.simplify $ reify act $ Stype maxBound)]
