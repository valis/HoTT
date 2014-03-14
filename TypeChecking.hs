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

maxType :: (Int,Int) -> (Int,Int) -> Expr -> Expr -> Value -> Value -> EDocM Value
maxType _ _ _ _ (Stype k1) (Stype k2) = Right $ Stype (max k1 k2)
maxType lc lc' e1 e2 t1 t2 = liftErr2 (error "maxType")
    (cmpTypesErr lc  (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr lc' (Stype $ pred maxBound) t2 e2)

processDefs :: [Def] -> [(String,Maybe Expr,[Arg],Expr)]
processDefs [] = []
processDefs (DefType _ t : Def (PIdent (_,name)) args e : defs) = (name,Just t,args,e) : processDefs defs
processDefs (Def (PIdent (_,name)) args e : defs) = (name,Nothing,args,e) : processDefs defs
processDefs _ = error "processDefs"

typeOf'depType :: Ctx -> [TypedVar] -> Expr -> EDocM Value
typeOf'depType ctx [] e = typeOf ctx e
typeOf'depType ctx (TypedVar _ vars t : list) e = do
    tv <- typeOf ctx t
    let lc = getPos t
        e' = Pi list e
    cmpTypesErr lc (Stype $ pred maxBound) tv t
    ctx' <- updateCtx ctx (evalRaw ctx t (Just tv)) vars
    ev <- typeOf ctx' e'
    maxType lc (getPos e) t e' tv ev
  where
    updateCtx ctx _ (Var (NoArg _)) = Right ctx
    updateCtx ctx tv (Var (Arg (PIdent (_,x)))) = Right (M.insert x (svar x,tv) ctx)
    updateCtx ctx tv (App a (Var (NoArg _))) = updateCtx ctx tv a
    updateCtx ctx tv (App a (Var (Arg (PIdent (_,x))))) = fmap (M.insert x (svar x,tv)) (updateCtx ctx tv a)
    updateCtx _ _ e = let (l,c) = getPos e in Left [emsgLC l c "Expected identifier" enull]

typeOf :: Ctx -> Expr -> EDocM Value
typeOf ctx (Lam _ [] e) = typeOf ctx e
typeOf _ (Lam (PLam ((l,c),_)) _ _) = Left [emsgLC l c "Cannot infer type of the argument" enull]
typeOf _ (Idp (PIdp ((l,c),_))) = Left [emsgLC l c "Cannot infer type of idp" enull]
typeOf ctx (Let defs e) = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    typeOf ctx' e
typeOf ctx (App (Idp _) e) = do
    t <- typeOf ctx e
    let v = evalRaw ctx e (Just t)
    Right (Sid t v v)
typeOf ctx (App (App (Idp _) e1) e2) = do
    t2 <- typeOf ctx e2
    case t2 of
        Sid s a b -> do
            t <- typeOfLam (getPos e2) ctx e1 e2 t2
            let e' = app 0 $ evalRaw ctx e1 (Just $ s `sarr` t)
            Right $ Sid t (e' a) (e' b)
        _ -> expTypeBut "Id" e2 t2
typeOf ctx (Arr e1 e2) =
    liftErr2 (maxType (getPos e1) (getPos e2) e1 e2) (typeOf ctx e1) (typeOf ctx e2)
typeOf ctx (Prod e1 e2) = typeOf ctx (Arr e1 e2)
typeOf ctx (Pi tv e) = typeOf'depType ctx tv e
typeOf ctx (Sigma tv e) = typeOf'depType ctx tv e
typeOf ctx (Id a b) = do
    a' <- typeOf ctx a
    b' <- typeOf ctx b
    cmpTypesErr (getPos b) a' b' b
    return $ typeOfTerm ctx (reify a')
typeOf _ (Nat _) = Right $ Stype (Finite 0)
typeOf _ (Universe (U (_,t))) = Right $ Stype $ succ (parseLevel t)
typeOf ctx (App e1 e2) = do
    t1 <- typeOf ctx e1
    case t1 of
        Spi _ _ a b -> hasType ctx e2 a >> Right (b $ evalRaw ctx e2 $ Just a)
        Sid (Spi x fv exp b) f g -> do
            b' <- isArr e1 t1 x fv b
            t2 <- typeOf ctx e2
            let (l,c) = getPos e2
            case t2 of
                Sid act x y -> case cmpTypes exp act of
                    Just o | o /= LT -> Right $ Sid b' (app 0 f x) (app 0 g y)
                    _ -> let em s t1 = s <> etext "(" <> epretty (T.simplify $ reify t1) <> etext ") _ _"
                         in Left [emsgLC l c "" $ em (etext "Expected type: Id") exp $$
                            em (etext "But term" <+> epretty e2 <+> etext "has type Id") act]
                _ -> expTypeBut "Id" e2 t2
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

isArr :: Expr -> Value -> String -> [String] -> (Value -> Value) -> EDocM Value
isArr e t x fv f =
    let x' = freshName x fv
        r = f (svar x')
    in if elem x' (valueFreeVars r)
        then expTypeBut "arrow" e t
        else Right r

typeOfLam :: (Int,Int) -> Ctx -> Expr -> Expr -> Value -> EDocM Value
typeOfLam lc' ctx (Lam _ [] e) e2 ty = typeOfLam lc' ctx e e2 ty
typeOfLam _ ctx (Lam (PLam ((l,c),_)) (x:xs) e) _ (Sid ty _ _) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        x' = unBinder x
    in do
        s <- typeOf (M.insert x' (svar x',ty) ctx) $ Lam (PLam (p,"\\")) xs e
        if elem x' $ T.freeVars (reify s)
            then Left [emsgLC l c "Cannot infer type of lambda expression" enull]
            else Right s
typeOfLam lc' ctx (Paren _ e) e2 act = typeOfLam lc' ctx e e2 act
typeOfLam (l',c') ctx e e2 (Sid act _ _) = do
    t <- typeOf ctx e
    case t of
        Spi x fv exp r -> case cmpTypes exp act of
            Just o | o /= LT -> isArr e t x fv r
            _ -> let em s t = s <> etext "(" <> epretty (T.simplify $ reify t) <> etext ") _ _"
                 in Left [emsgLC l' c' "" $ em (etext "Expected type: Id") exp $$
                    em (etext "But term" <+> epretty e2 <+> etext "has type Id") act]
        _ -> expTypeBut "pi" e t
typeOfLam _ _ _ _ _ = error "typeOfLam"

hasType :: Ctx -> Expr -> Value -> EDocM ()
hasType ctx (Lam _ [] e) ty = hasType ctx e ty
hasType ctx (Lam i (x:xs) e) (Spi z fv a b) =
    let (x',e') = renameExpr fv (unBinder x) (Lam i xs e)
    in hasType (M.insert x' (svar x',a) ctx) e' $ b (svar x')
hasType _ (Lam _ (Binder arg : _) _) ty =
    let (l,c) = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    in Left [emsgLC l c "" $ expType 1 ty $$ etext "But lambda expression has pi type"]
hasType _ i@(Idp (PIdp (lc,_))) exp@(Spi x _ a _) =
    cmpTypesErr lc exp (Spi x (valueFreeVars a) a $ \v -> Sid a v v) i
hasType _ (Idp (PIdp ((l,c),_))) ty =
    Left [emsgLC l c "" $ expType 1 ty $$ etext "But idp has pi type"]
hasType ctx i@(App (Idp (PIdp ((l,c),_))) e) exp@(Spi x fv (Sid t a b) r) =
    let x' = freshName x fv
    in case r (svar x') of
        Sid s _ _ -> do
            hasType ctx e (t `sarr` s)
            let e' = evalRaw ctx e (Just $ t `sarr` s)
                act = Sid t a b `sarr` Sid s (app 0 e' a) (app 0 e' b)
            cmpTypesErr (l,c) exp act i
        Spi _ _ _ _ ->
            let (l',c') = getPos e
            in Left [emsgLC l' c' "cannot infer type of the second argument" enull]
        _ -> Left [emsgLC l c "" $ expType 2 exp $$ etext "But idp _ has type of the form x = y -> _ x = _ y"]
hasType _ (App (Idp (PIdp ((l,c),_))) _) exp@(Spi _ _ _ _) =
    Left [emsgLC l c "" $ expType 2 exp $$ etext "But idp _ has type of the form x = y -> _ x = _ y"]
hasType ctx e@(App (Idp _) _) exp@(Sid _ _ _) = do
    act <- typeOf ctx e
    cmpTypesErr (getPos e) exp act e
hasType _ (App (Idp (PIdp ((l,c),_))) _) exp =
    Left [emsgLC l c "" $ expType 1 exp $$ etext "But idp _ has Id type"]
hasType ctx (Paren _ e) ty = hasType ctx e ty
hasType ctx (Let defs e) ty = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    hasType ctx' e ty
hasType ctx e exp = do
    act <- typeOf ctx e
    cmpTypesErr (getPos e) exp act e

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
expType l ty = etext "Expected type:" <+> eprettyLevel l (T.simplify $ reify ty)

cmpTypesErr :: (Int,Int) -> Value -> Value -> Expr -> EDocM ()
cmpTypesErr (l,c) t1 t2 e = case cmpTypes t1 t2 of
    Just o | o /= LT -> Right ()
    _ -> Left [emsgLC l c "" $ expType (-1) t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> epretty (T.simplify $ reify t2)]

expTypeBut :: String -> Expr -> Value -> EDocM a
expTypeBut exp e act =
    let (l,c) = getPos e
    in Left [emsgLC l c "" $ etext ("Expected " ++ exp ++ " type") $$
            etext "But term" <+> epretty e <+> etext "has type" <+> eprettyHead (T.simplify $ reify act)]
