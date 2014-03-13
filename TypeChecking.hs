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
maxType (l,c) (l',c') e1 e2 t1 t2 = liftErr2 (error "maxType")
    (cmpTypesErr l  c  (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr l' c' (Stype $ pred maxBound) t2 e2)

processDefs :: [Def] -> [(String,Maybe Expr,[Arg],Expr)]
processDefs [] = []
processDefs (DefType _ t : Def (PIdent (_,name)) args e : defs) = (name,Just t,args,e) : processDefs defs
processDefs (Def (PIdent (_,name)) args e : defs) = (name,Nothing,args,e) : processDefs defs
processDefs _ = error "processDefs"

typeOf'depType :: Ctx -> [TypedVar] -> Expr -> EDocM Value
typeOf'depType ctx [] e = typeOf ctx e
typeOf'depType ctx (TypedVar _ vars t : list) e = do
    tv <- typeOf ctx t
    let (l,c) = getPos t
        e' = Pi list e
    cmpTypesErr l c (Stype $ pred maxBound) tv t
    ctx' <- updateCtx ctx (evalRaw ctx t (Just tv)) vars
    ev <- typeOf ctx' e'
    maxType (l,c) (getPos e) t e' tv ev
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
typeOf _ (Pmap (Ppmap ((l,c),_)) _) = Left [emsgLC l c "Cannot infer type of pmap" enull]
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
typeOf ctx (App (Pmap (Ppmap ((l,c),_)) e1) e2) = do
    t2 <- typeOf ctx e2
    case t2 of
        Sid s a b -> do
            t <- typeOfLam (l,c) (getPos e2) ctx e1 e2 t2
            let e' = app 0 $ evalRaw ctx e1 (Just $ s `sarr` t)
            Right $ Sid t (e' a) (e' b)
        _ -> let (l',c') = getPos e2
             in Left [emsgLC l' c' "" $ etext "Expected Id type" $$ etext "But term" <+> epretty e2
                    <+> etext "has type" <+> eprettyHead (reify t2)]
typeOf ctx (Arr e1 e2) =
    liftErr2 (maxType (getPos e1) (getPos e2) e1 e2) (typeOf ctx e1) (typeOf ctx e2)
typeOf ctx (Prod e1 e2) = typeOf ctx (Arr e1 e2)
typeOf ctx (Pi tv e) = typeOf'depType ctx tv e
typeOf ctx (Sigma tv e) = typeOf'depType ctx tv e
typeOf ctx (Id a b) = do
    a' <- typeOf ctx a
    b' <- typeOf ctx b
    let (l,c) = getPos b
    cmpTypesErr l c a' b' b
    return $ typeOfTerm ctx (reify a')
typeOf _ (Nat _) = Right $ Stype (Finite 0)
typeOf _ (Universe (U (_,t))) = Right $ Stype $ succ (parseLevel t)
typeOf ctx (App e1 e2) = do
    t <- typeOf ctx e1
    case t of
        Spi _ _ a b -> hasType ctx e2 a >> Right (b $ evalRaw ctx e2 $ Just a)
        _ -> let (l,c) = getPos e1
             in Left [emsgLC l c "" $ etext "Expected pi type" $$
                    etext "But term" <+> epretty e1 <+> etext "has type" <+> eprettyHead (reify t)]
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

typeOfLam :: (Int,Int) -> (Int,Int) -> Ctx -> Expr -> Expr -> Value -> EDocM Value
typeOfLam lc lc' ctx (Lam _ [] e) e2 ty = typeOfLam lc lc' ctx e e2 ty
typeOfLam _ _ ctx (Lam (PLam ((l,c),_)) (x:xs) e) _ (Sid ty _ _) =
    let p = if null xs then getPos e else binderGetPos (head xs)
        (x',e') = renameExpr [] (unBinder x) (Lam (PLam (p,"\\")) xs e)
    in do
        s <- typeOf (M.insert x' (svar x',ty) ctx) e'
        if elem x' $ T.freeVars (reify s)
            then Left [emsgLC l c "Cannot infer type of lambda expression" enull]
            else Right s
typeOfLam lc lc' ctx (Paren _ e) e2 act = typeOfLam lc lc' ctx e e2 act
typeOfLam (l,c) (l',c') ctx e e2 (Sid act _ _) = do
    t <- typeOf ctx e
    case t of
        Spi x fv exp r -> do
            case cmpTypes exp act of
                Just o | o /= LT -> Right ()
                _ -> let em s t = s <> etext "(" <> epretty (T.simplify $ reify t) <> etext ") _ _"
                     in Left [emsgLC l' c' "" $ em (etext "Expected type: Id") exp $$
                        em (etext "But term" <+> epretty e2 <+> etext "has type Id") act]
            let x' = freshName x fv
                r' = r (svar x')
            if elem x' $ T.freeVars (reify r')
                then Left [emsgLC l c "" $ etext "Expected arrow type" $$ etext "But term" <+>
                    epretty e <+> etext "has type" <+> epretty (reify t)]
                else Right r'
        _ -> Left [emsgLC l c "" $ etext "Expected pi type" $$ etext "But term" <+> epretty e
                <+> etext "has type" <+> eprettyHead (reify t)]
typeOfLam _ _ _ _ _ _ = error "typeOfLam"

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
hasType _ i@(Idp (PIdp ((l,c),_))) exp@(Spi x _ a _) =
    cmpTypesErr l c exp (Spi x (valueFreeVars a) a $ \v -> Sid a v v) i
hasType _ (Idp (PIdp ((l,c),_))) ty =
    Left [emsgLC l c "" $ expType 1 ty $$ etext "But idp has pi type"]
hasType ctx i@(Pmap (Ppmap ((l,c),_)) e) exp@(Spi x fv (Sid t a b) r) =
    let x' = freshName x fv
    in case r (svar x') of
        Sid s _ _ -> do
            hasType ctx e (t `sarr` s)
            let e' = evalRaw ctx e (Just $ t `sarr` s)
                act = Sid t a b `sarr` Sid s (app 0 e' a) (app 0 e' b)
            cmpTypesErr l c exp act i
        _ -> Left [emsgLC l c "" $ expType 2 exp $$ etext "But pmap _ has type of the form x = y -> _ x = _ y"]
hasType _ (Pmap (Ppmap ((l,c),_)) _) exp@(Spi _ _ _ _) =
    Left [emsgLC l c "" $ expType 2 exp $$ etext "But pmap _ has type of the form x = y -> _ x = _ y"]
hasType _ (Pmap (Ppmap ((l,c),_)) _) exp =
    Left [emsgLC l c "" $ expType 1 exp $$ etext "But pmap _ has pi type"]
hasType ctx (Paren _ e) ty = hasType ctx e ty
hasType ctx (Let defs e) ty = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    hasType ctx' e ty
hasType ctx e ty = do
    ty1 <- typeOf ctx e
    let (l,c) = getPos e
    cmpTypesErr l c ty ty1 e

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
expType l ty = etext "Expected type:" <+> eprettyLevel l (reify ty)

cmpTypesErr :: Int -> Int -> Value -> Value -> Expr -> EDocM ()
cmpTypesErr l c t1 t2 e = case cmpTypes t1 t2 of
    Just o | o /= LT -> Right ()
    _ -> Left [emsgLC l c "" $ expType (-1) t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> epretty (reify t2)]
