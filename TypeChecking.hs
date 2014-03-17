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

data H = P Expr Value | T Value | N

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
typeOfH ctx (Lam (PLam (lc,_)) (x:xs) e) (P _ (Sid ty _ _)) = do
    let p = if null xs then getPos e else binderGetPos (head xs)
        (x',e') = renameExpr (freeVars $ Lam (PLam (p,"\\")) xs e) (unBinder x) $ Lam (PLam (p,"\\")) xs e
    s <- typeOf (M.insert x' (svar x' ty,ty) ctx) e'
    if elem x' $ T.freeVars (reifyType s)
        then inferErrorMsg lc "lambda expression"
        else Right s
typeOfH ctx e (P e2 (Sid act _ _)) = do
    t <- typeOf ctx e
    case t of
        Spi x fv exp r -> if cmpTypes act exp
            then case isArr x fv exp r of
                Just r' -> Right r'
                Nothing -> expTypeBut "arrow" e t
            else let em s t = s <> etext "(" <> eprettyType t <> etext ") _ _"
                     (l,c) = getPos e2
                 in Left [emsgLC l c "" $ em (etext "Expected type: Id") exp $$
                    em (etext "But term" <+> epretty e2 <+> etext "has type Id") act]
        _ -> expTypeBut "pi" e t
typeOfH ctx (Lam _ (x:xs) e) (T r@(Spi z fv a b)) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        (x',e') = renameExpr fv (unBinder x) (Lam (PLam (p,"\\")) xs e)
        v = svar x' a
    in typeOfH (M.insert x' (v,a) ctx) e' (T (b v)) >> return r
typeOfH _ (Lam _ (Binder arg : _) _) (T ty) =
    let (l,c) = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    in Left [emsgLC l c "" $ expType 1 ty $$ etext "But lambda expression has pi type"]
typeOfH _ i@(Idp _) (T exp@(Spi x _ a _)) = do
    cmpTypesErr exp (Spi x (valueFreeVars a) a $ \v -> Sid a v v) i
    return exp
typeOfH _ (Idp (PIdp ((l,c),_))) (T ty) =
    Left [emsgLC l c "" $ expType 1 ty $$ etext "But idp has pi type"]
typeOfH ctx e@(Trans (PTrans (lc,_))) (T ty@(Spi v fv a@(Sid (Stype _) x y) b)) = case b $ svar (freshName v fv) a of
    Spi v' fv' x' y' -> if cmpTypes x x' && cmpTypes y (y' $ svar (freshName v' fv') x')
        then return ty
        else transErrorMsg lc ty
    _ -> transErrorMsg lc ty
typeOfH ctx (Trans (PTrans (lc,_))) (T ty) = transErrorMsg lc ty
typeOfH ctx ea@(App e1 e) (T exp@(Sid t a b)) | Idp _ <- dropParens e1 = do
    typeOfH ctx e (T t)
    let e' = evalRaw ctx e (Just t)
    cmpTypesErr exp (Sid t e' e') ea
    return exp
typeOfH ctx (App e1 _) (T exp) | Idp (PIdp ((l,c),_)) <- dropParens e1 =
    Left [emsgLC l c "" $ expType 1 exp $$ etext "But idp _ has Id type"]
-- pmap :: Id (A -> B) f g -> Id A x y -> Id B (f x) (g y)
typeOfH ctx (Pmap (Ppmap (lc,_))) (T exp@(Spi v fv a@(Sid (Spi v' fv' a' b') f g) b)) =
    case (isArr v fv a b, isArr v' fv' a' b') of
        (Just (Spi v2 fv2 a2'@(Sid a2 x y) b2'), Just t) | Just (Sid b2 x' y') <- isArr v2 fv2 a2' b2', cmpTypes a2 a'
            && cmpTypes t b2 && reify x' b2 == reify (app 0 f x) t && reify y' b2 == reify (app 0 g y) t -> return exp
        _ -> extErrorMsg lc exp
typeOfH ctx (Pmap (Ppmap (lc,_))) (T exp) = extErrorMsg lc exp
typeOfH ctx ea@(App e1 e) (T ty@(Spi v fv a'@(Sid a x y) b')) | Pmap (Ppmap ((l,c),_)) <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid (Spi v1 fv1 a1 b1') f g | Just b1 <- isArr v1 fv1 a1 b1' -> if cmpTypes a a1
            then cmpTypesErr ty (a' `sarr` Sid b1 (app 0 f x) (app 0 g y)) ea >> return ty
            else Left [emsgLC l c "" $ expType (-1) ty $$ etext "But term" <+> epretty ea <+>
                 etext "has type of the form Id" <+> epretty (reifyType a1) <+> etext "_ _ -> Id _ _ _"]
        _ -> pmapErrorMsg (l,c) ty
typeOfH ctx (App e1 e) (T ty) | Pmap (Ppmap (lc,_)) <- dropParens e1 = pmapErrorMsg lc ty
typeOfH _ (Lam (PLam (lc,_)) _ _) _ = inferErrorMsg lc "the argument"
typeOfH _ (Idp (PIdp (lc,_))) _ = inferErrorMsg lc "idp"
typeOfH _ (Trans (PTrans (lc,_))) _ = inferErrorMsg lc "trans"
typeOfH ctx (App e1 e) _ | Idp _ <- dropParens e1 = do
    t <- typeOf ctx e
    let v = evalRaw ctx e (Just t)
    Right (Sid t v v)
typeOfH _ (Pmap (Ppmap (lc,_))) _ = inferErrorMsg lc "ext"
typeOfH ctx (Ext (PExt (lc,_))) (T ty@(Spi x' fv' s@(Spi _ _ a' b') t)) = case isArr x' fv' s t of
    Just (Sid (Spi x fv a b) f g) | cmpTypes a a' ->
        let v = svar (freshName x $ fv `union` fv' `union` valueFreeVars f `union` valueFreeVars g) a
        in if cmpTypes (b' v) (Sid (b v) (app 0 f v) (app 0 g v)) then Right ty else extErrorMsg lc ty
    _ -> extErrorMsg lc ty
typeOfH ctx (Ext (PExt (lc,_))) (T ty) = extErrorMsg lc ty
typeOfH ctx (Ext (PExt (lc,_))) _ = inferErrorMsg lc "ext"
typeOfH ctx (App e1 e) (T r@(Sid (Spi x fv a b) f g)) | Ext _ <- dropParens e1 = do
    typeOfH ctx e $ T $ Spi x (fv `union` valueFreeVars f `union` valueFreeVars g) a $ \v -> Sid (b v) (app 0 f v) (app 0 g v)
    return r
typeOfH ctx ea@(App e1 e) (T exp) | Ext (PExt ((l,c),_)) <- dropParens e1 = Left [emsgLC l c "" $ expType (-1) exp
    $$ etext "But term" <+> epretty ea <+> etext "has type of the form Id ((x : A) -> B x) _ _"]
typeOfH ctx e (T exp) = do
    act <- typeOf ctx e
    cmpTypesErr exp act e
    return exp
typeOfH _ (App e1 _) _ | Pmap (Ppmap (lc,_)) <- dropParens e1 = inferErrorMsg lc "ext"
-- pmap (idp e1) e2
typeOfH ctx (App e1' e2) _
    | App e3 e4 <- dropParens e1'
    , Pmap _ <- dropParens e3
    , App e5 e1 <- dropParens e4
    , Idp _ <- dropParens e5 = do
        t2 <- typeOf ctx e2
        case t2 of
            Sid s a b -> do
                t <- typeOfH ctx e1 (P e2 t2)
                let e' = evalRaw ctx e1 $ Just (s `sarr` t)
                Right $ Sid t (app 0 e' a) (app 0 e' b)
            _ -> expTypeBut "Id" e2 t2
typeOfH ctx (App e1' e2) _ | App e3 e1 <- dropParens e1', Pmap _ <- dropParens e3 = do
    r <- liftErr2' (,) (typeOf ctx e1) (typeOf ctx e2)
    case r of
        (Sid (Spi v fv a b') f g, Sid t x y) | Just b <- isArr v fv a b' -> if cmpTypes t a
            then Right $ Sid b (app 0 f x) (app 0 g y)
            else errMsg e2 t (eprettyType a)
        (Sid t1 _ _, Sid _ _ _) -> errMsg e1 t1 (etext "_ -> _")
        (t1, Sid _ _ _) -> expTypeBut "Id" e1 t1
        (_, t2) -> expTypeBut "Id" e2 t2
  where
    errMsg expr ty i =
        let (l,c) = getPos expr
        in Left [emsgLC l c "" $ etext "Expected type of the form Id(" <> i <> etext ") _ _" $$
                 etext "But term" <+> epretty expr <+> etext "has type Id(" <> eprettyType ty <> etext ") _ _"]
typeOfH ctx (App e1 e) _ | Trans _ <- dropParens e1 = do
    t <- typeOf ctx e
    case t of
        Sid (Stype _) x y -> Right (x `sarr` y)
        _ -> expTypeBut "Id Type _ _" e t
typeOfH ctx (Arr e1 e2) _ =
    liftErr2 (maxType e1 e2) (typeOf ctx e1) (typeOf ctx e2)
typeOfH ctx (Prod e1 e2) _ = typeOf ctx (Arr e1 e2)
typeOfH ctx (Pi tv e) _ = typeOf'depType ctx tv e
typeOfH ctx (Sigma tv e) _ = typeOf'depType ctx tv e
typeOfH ctx (Id a b) _ = do
    a' <- typeOf ctx a
    typeOfH ctx b (T a')
    return $ typeOfTerm ctx (reifyType a')
typeOfH _ (Nat _) _ = Right $ Stype (Finite 0)
typeOfH _ (Universe (U (_,t))) _ = Right $ Stype $ succ (parseLevel t)
typeOfH ctx (App e1 e2) _ = do
    t1 <- typeOf ctx e1
    case t1 of
        Spi _ _ a b -> do
            typeOfH ctx e2 (T a)
            return $ b $ evalRaw ctx e2 (Just a)
        _ -> expTypeBut "pi" e1 t1
typeOfH _ (Var (NoArg (Pus ((l,c),_)))) _ = Left [emsgLC l c "Expected identifier" enull]
typeOfH ctx (Var (Arg (PIdent ((l,c),x)))) _ = case M.lookup x ctx of
    Nothing -> Left [emsgLC l c ("Unknown identifier " ++ x) enull]
    Just (_,t) -> Right t
typeOfH _ (Suc _) _ = Right (sarr Snat Snat)
typeOfH _ (NatConst _) _ = Right Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfH _ (Rec _) _ = Right $ Spi "P" [] (Snat `sarr` Stype maxBound) $ \p ->
    let pfv = valueFreeVars p
    in app 0 p Szero `sarr` (Spi "x" pfv Snat $ \x -> app 0 p x `sarr` app 0 p (Ssuc x)) `sarr` Spi "x" pfv Snat (app 0 p)
typeOfH ctx (Typed e t) _ = do
    typeOfH ctx t $ T (Stype maxBound)
    typeOfH ctx e $ T $ evalRaw ctx t $ Just (Stype maxBound)

isArr :: String -> [String] -> Value -> (Value -> Value) -> Maybe Value
isArr x fv t f =
    let x' = freshName x fv
        r = f (svar x' t)
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
inferErrorMsg (l,c) s = Left [emsgLC l c ("Cannot infer type of " ++ s) enull]

transErrorMsg :: (Int,Int) -> Value -> EDocM a
transErrorMsg (l,c) ty =
    Left [emsgLC l c "" $ expType 1 ty $$ etext "But trans has type of the form Id Type A B -> A -> B"]

pmapErrorMsg :: (Int,Int) -> Value -> EDocM a
pmapErrorMsg (l,c) ty = Left [emsgLC l c "" $ expType (-1) ty $$ etext "But ext _ has type of the form x = y -> _ x = _ y"]

extErrorMsg :: (Int,Int) -> Value -> EDocM a
extErrorMsg (l,c) exp = Left [emsgLC l c "" $ expType (-1) exp $$
    etext "But term ext has type of the form ((x : A) -> f x = g x) -> f = g"]

expType :: Int -> Value -> EDoc
expType l ty = etext "Expected type:" <+> eprettyLevel l (T.simplify $ reifyType ty)

cmpTypesErr :: Value -> Value -> Expr -> EDocM ()
cmpTypesErr t1 t2 e = if cmpTypes t2 t1
    then Right ()
    else let (l,c) = getPos e in Left [emsgLC l c "" $ expType (-1) t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> eprettyType t2]

expTypeBut :: String -> Expr -> Value -> EDocM a
expTypeBut exp e act =
    let (l,c) = getPos e
    in Left [emsgLC l c "" $ etext ("Expected " ++ exp ++ " type") $$
            etext "But term" <+> epretty e <+> etext "has type" <+> eprettyHead (T.simplify $ reifyType act)]
