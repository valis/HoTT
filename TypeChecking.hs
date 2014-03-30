module TypeChecking
    ( typeOf
    , evalDecl, processDefs
    , TCM(..)
    ) where

import qualified Data.Map as M
import Data.List

import ErrorDoc
import Value
import Parser.AbsGrammar
import Syntax.Common
import Syntax.Raw
import qualified Syntax.Term as T
import RawToTerm
import Eval

newtype TCM a = TCM { runTCM :: T.DBIndex -> [String] -> M.Map String T.DBIndex -> Ctx -> EDocM a }

instance Functor TCM where
    fmap f (TCM m) = TCM $ \a b c d -> fmap f (m a b c d)

instance Monad TCM where
    return x = TCM $ \_ _ _ _ -> return x
    TCM f >>= k = TCM $ \a b c d -> f a b c d >>= \r -> runTCM (k r) a b c d

liftTCM2' :: (a -> b -> c) -> TCM a -> TCM b -> TCM c
liftTCM2' f (TCM m1) (TCM m2) = TCM $ \a b c d -> liftErr2 f (m1 a b c d) (m2 a b c d)

liftTCM2 :: (a -> b -> TCM c) -> TCM a -> TCM b -> TCM c
liftTCM2 f m1 m2 = do
    (r1,r2) <- liftTCM2' (,) m1 m2
    f r1 r2

ask :: TCM (T.DBIndex, [String], M.Map String T.DBIndex, Ctx)
ask = TCM $ \a b c d -> return (a, b, c, d)

local :: (T.DBIndex -> [String] -> M.Map String T.DBIndex -> Ctx -> (T.DBIndex, [String], M.Map String T.DBIndex, Ctx))
    -> TCM a -> TCM a
local f (TCM m) = TCM $ \a b c d ->
    let (a',b',c',d') = f a b c d
    in m a' b' c' d'

liftEDocM :: EDocM a -> TCM a
liftEDocM m = TCM $ \_ _ _ _ -> m

errorTCM :: EMsg -> TCM a
errorTCM e = liftEDocM $ Left [e]

maxType :: Expr -> Expr -> Value -> Value -> TCM Value
maxType _ _ (Stype k1) (Stype k2) = return $ Stype (max k1 k2)
maxType e1 e2 t1 t2 = liftTCM2 (error "maxType")
    (cmpTypesErr (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr (Stype $ pred maxBound) t2 e2)

processDefs :: [Def] -> [(String,Maybe Expr,[Arg],Expr)]
processDefs [] = []
processDefs (DefType _ t : Def (PIdent (_,name)) args e : defs) = (name,Just t,args,e) : processDefs defs
processDefs (Def (PIdent (_,name)) args e : defs) = (name,Nothing,args,e) : processDefs defs
processDefs _ = error "processDefs"

typeOf'depType :: [TypedVar] -> Expr -> TCM Value
typeOf'depType [] e = typeOf e
typeOf'depType (TypedVar _ vars t : list) e = do
    tv <- typeOf t
    cmpTypesErr (Stype $ pred maxBound) tv t
    (i,_,mctx,ctx) <- ask
    r <- case exprToVars vars of
        Just l -> updateCtx (evalRaw i mctx ctx t Nothing) l
        Nothing -> errorTCM $ emsgLC (getPos e) "Expected identifier" enull
    local (\_ _ _ _ -> r) $ do
        ev <- typeOf (Pi list e)
        maxType t (Pi list e) tv ev
  where
    updateCtx _ [] = ask
    updateCtx tv (NoArg _ : as) =
        local (\i c mctx (ctx,lctx) -> (i + 1, "_" : c, mctx, (ctx, (svar i tv, tv) : lctx))) (updateCtx tv as)
    updateCtx tv (Arg (PIdent (_,x)) : as) =
        local (\i c mctx (ctx,lctx) -> (i + 1, x : c, M.insert x i mctx, (ctx, (svar i tv, tv) : lctx))) (updateCtx tv as)
    
    exprToVars :: Expr -> Maybe [Arg]
    exprToVars = fmap reverse . go
      where
        go (Var a) = Just [a]
        go (App as (Var a)) = fmap (a :) (go as)
        go _ = Nothing

dropParens :: Expr -> Expr
dropParens (Paren _ e) = dropParens e
dropParens e = e

data H = P Expr Value Value Value | T Value | N

typeOf :: Expr -> TCM Value
typeOf e = typeOfH e N

typeOfH :: Expr -> H -> TCM Value
typeOfH (Let defs e) h = do
    defs' <- liftEDocM (preprocessDefs defs)
    (mctx,ctx) <- go (processDefs defs')
    local (\i c _ _ -> (i,c,mctx,ctx)) (typeOfH e h)
  where
    go [] = fmap (\(_,_,mctx,ctx) -> (mctx,ctx)) ask
    go ((name,ty,args,expr):ds) = do
        let p = if null args then getPos expr else argGetPos (head args)
        (mctx',ctx',_,_) <- evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
        local (\i c _ _ -> (i,c,mctx',ctx')) (go ds)
typeOfH (Paren _ e) h = typeOfH e h
typeOfH (Lam _ [] e) h = typeOfH e h

typeOfH e1@(Lam (PLam (lc,_)) (x:xs) e) (P _ ty a b) = do
    let p = if null xs then getPos e else binderGetPos (head xs)
        e' = Lam (PLam (p,"\\")) xs e
        x' = unBinder x
    s <- local (\i c mctx (ctx,lctx) -> (i + 1, x' : c, M.insert x' i mctx, (ctx, (svar i ty,ty) : lctx))) (typeOf e')
    (i,_,mctx,ctx) <- ask
    if isFreeVar 0 (i + 1) s
        then inferErrorMsg lc "lambda expression"
        else let v1 = evalRaw i mctx ctx e1 $ Just (ty `sarr` s)
             in return $ Sid s (app 0 v1 a) (app 0 v1 b)
typeOfH e1 (P e2 act a b) = do
    t1 <- typeOf e1
    (i,_,mctx,ctx) <- ask
    let v1 = evalRaw i mctx ctx e1 Nothing
    typeOfPmap t1 v1 v1 (Sid act a b) e1 e2

typeOfH (Lam _ (x:xs) e) (T r@(Spi z a b)) = do
    (i,_,_,_) <- ask
    let p = if null xs then getPos e else binderGetPos (head xs)
        v = svar i a
        x' = unBinder x
    local (\i c mctx (ctx,lctx) -> (i + 1, x' : c, M.insert x' i mctx, (ctx, (v,a) : lctx))) $
        typeOfH (Lam (PLam (p,"\\")) xs e) $ T (b 0 [] v)
    return r
typeOfH (Lam _ (Binder arg : _) _) (T ty) = do
    let lc = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But lambda expression has pi type"
typeOfH j@(Idp _) (T exp@(Spi x a _)) = do
    let ctx = (M.singleton (freshName "a" [x]) (a,Stype maxBound), [])
    cmpTypesErr exp (eval 0 ctx $ T.Pi [([x],T.Var "a")] $ T.Id (T.Var "a") (T.LVar 0) (T.LVar 0)) j
    return exp
typeOfH (Idp (PIdp (lc,_))) (T ty) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But idp has pi type"
typeOfH e@(Coe (PCoe (lc,_))) (T ty@(Spi v a@(Sid (Stype _) x y) b)) = do
    (i,_,_,_) <- ask
    case b 0 [] $ svar i a of
        Spi v' x' y' -> if cmpTypes i x x' && cmpTypes (i + 1) y (y' 0 [] $ svar i x') -- ???
            then return ty
            else coeErrorMsg lc ty
        _ -> coeErrorMsg lc ty
typeOfH (Coe (PCoe (lc,_))) (T ty) = coeErrorMsg lc ty
typeOfH ea@(App e1 e) (T exp@(Sid t a b)) | Idp _ <- dropParens e1 = do
    (i,_,mctx,ctx) <- ask
    typeOfH e (T t)
    let e' = evalRaw i mctx ctx e (Just t)
    cmpTypesErr exp (Sid t e' e') ea
    return exp
typeOfH (App e1 _) (T exp) | Idp (PIdp (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 exp $$ etext "But idp _ has Id type"
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfH e@(Pmap (Ppmap (lc,_))) (T exp@(Spi v a@(Sid (Spi v' a' b') f g) b)) = do
    (i,_,_,_) <- ask
    case isArr i a b of
        Just (Spi v2 a2'@(Sid a2 x y) b2') | cmpTypes i a2 a' -> do
            let ctx' = [("a",(a,Stype maxBound)),("a'",(a',Stype maxBound)),("x",(x,a2)),("y",(y,a2)),("B",(Slam v' b',a' `sarr` Stype maxBound)),("f'",(app 0 f x,b' 0 [] x)),("g'",(app 0 g y,b' 0 [] y))]
                term = T.Pi [([],T.Var "a")] $ T.Pi [(["p"],T.Id (T.Var "a'") (T.Var "x") (T.Var "y"))] $
                    T.Id (T.Var "B" `T.App` T.Var "y")
                         (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.LVar 0) `T.App` T.Var "f'")
                         (T.Var "g'")
            cmpTypesErr exp (eval 0 (M.fromList ctx', []) term) e
            return exp
        _ -> pmapErrorMsg lc exp
typeOfH (Pmap (Ppmap (lc,_))) (T exp) = pmapErrorMsg lc exp
typeOfH ea@(App e1 e) (T ty@(Spi v a'@(Sid a x y) b')) | Pmap _ <- dropParens e1 = do
    t <- typeOf e
    (i,c,_,_) <- ask
    case t of
        Sid (Spi v1 a1 b1) f g | cmpTypes i a a1 -> do
            let ctx' = [("a'",(a',Stype maxBound)),("B",(Slam v1 b1,a1 `sarr` Stype maxBound)),("y",(y,a)),("f'",(app 0 f x,b1 0 [] x)),("g'",(app 0 g y,b1 0 [] y))]
                term = T.Pi [(["p"],T.Var "a'")] $ T.Id (T.Var "B" `T.App` T.Var "y")
                    (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.LVar 0) `T.App` T.Var "f'")
                    (T.Var "g'")
            cmpTypesErr ty (eval 0 (M.fromList ctx', []) term) ea
            return ty
        _ -> errorTCM $ emsgLC (getPos e) "" $
            etext "Expected type: Id(" <+> epretty c (T.Pi [([],reifyType i a)] $ T.Var "_") <+> etext ") _ _" $$
            etext "But term" <+> eprettyExpr e <+> etext "has type" <+> epretty c (reifyType i t)
typeOfH (App e1 e) (T ty) | Pmap (Ppmap (lc,_)) <- dropParens e1 = pmap1ErrorMsg lc ty
typeOfH (Ext (PExt (lc,_))) (T ty@(Spi x' s@(Spi _ a' b') t)) = do
    (i,_,_,_) <- ask
    case isArr i s t of
        Just (Sid (Spi _ a b) f g) | cmpTypes i a a' ->
            let v = svar i a
            in if cmpTypes (i + 1) (b' 0 [] v) (Sid (b 0 [] v) (app 0 f v) (app 0 g v))
                then return ty
                else extErrorMsg lc ty
        _ -> extErrorMsg lc ty
-- ext : (s : Id A x x') * Id (B x') (trans B s y) y' -> Id ((x : A) * B x) (x,y) (x',y')
--       a'              * b'                         -> Id (a       * b  ) p     q
typeOfH (Ext (PExt (lc,_))) (T ty@(Spi x' s@(Ssigma _ a' b') t)) = do
    (i,_,_,_) <- ask
    case isArr i s t of
        Just (Sid (Ssigma x a b) p q) ->
            let v = svar i $ Sid a (proj1 p) (proj1 q)
            in if cmpTypes i a' (Sid a (proj1 p) (proj1 q)) &&
                  cmpTypes (i + 1) (b' 0 [] v) (Sid (b 0 [] $ proj1 q) (trans 0 (Slam x b) s $ proj2 p) (proj2 q))
               then return ty
               else extErrorMsg lc ty
        _ -> extErrorMsg lc ty
typeOfH (Ext (PExt (lc,_))) (T ty) = extErrorMsg lc ty
typeOfH (App e1 e) (T r@(Sid (Spi x a b) f g)) | Ext _ <- dropParens e1 = do
    typeOfH e $ T $ Spi x a $ \k m v -> Sid (b k m v) (app k (action m f) v) (app k (action m g) v)
    return r
-- (s : Id a (proj1 p) (proj1 q)) * (Id (B (proj1 q)) (trans B s (proj2 p)) (proj2 q))
typeOfH (App e1 e) (T r@(Sid (Ssigma x a b) p q)) | Ext _ <- dropParens e1 = do
    typeOfH e $ T $ Ssigma x (Sid a (proj1 p) (proj1 q)) $ \k m s ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x b) s $ action m (proj2 p)
            r3 = action m (proj2 q)
        in eval k (M.fromList [("r1",(r1,Stype maxBound)),("r2",(r2,r1)),("r3",(r3,r1))], []) $ T.Id (T.Var "r1") (T.Var "r2") (T.Var "r3")
    return r
typeOfH (App e1 e) (T exp) | Ext (PExt (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
        etext "But term ext _ has type either of the form Id ((x : A) -> B x) _ _ or of the form Id ((x : A) * B x) _ _"
typeOfH (App e1 e) (T exp@(Sid t x y)) | Inv _ <- dropParens e1 = do
    typeOfH e $ T (Sid t y x)
    return exp
typeOfH (App e1 e) (T exp) | Inv (PInv (lc,_)) <- dropParens e1 = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But term inv _ has Id type"
typeOfH (Pair e1 e2) (T r@(Ssigma _ a b)) = do
    (i,_,mctx,ctx) <- ask
    typeOfH e1 (T a)
    typeOfH e2 $ T $ b 0 [] $ evalRaw i mctx ctx e1 (Just a)
    return r
typeOfH e@(Pair _ _) (T exp) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos e) "" $ expType i c (-1) exp $$ etext "But term" <+> eprettyExpr e <+> etext "has Sigma type"
typeOfH (Proj1 (PProjl (lc,_))) (T r@(Spi x a'@(Ssigma _ a _) b)) = do
    (i,_,_,_) <- ask
    case isArr i a' b of
        Just b' | cmpTypes i a b' -> return r
        _ -> proj1ErrorMsg lc r
typeOfH (Proj1 (PProjl (lc,_))) (T exp) = proj1ErrorMsg lc exp
-- proj2 : (p : (x : A) -> B x) -> B (proj1 p)
typeOfH (Proj2 (PProjr (lc,_))) (T r@(Spi x a'@(Ssigma _ a b) b')) = do
    (i,_,_,_) <- ask
    if cmpTypes (i + 1) (b 0 [] $ liftTerm (\l -> T.App T.Proj1 $ T.LVar $ l - i - 1) a) (b' 0 [] $ svar i a')
        then return r
        else proj2ErrorMsg lc r
typeOfH (Proj2 (PProjr (lc,_))) (T exp) = proj2ErrorMsg lc exp
typeOfH (Comp (PComp (lc,_))) (T exp) = do
    (i,c,_,_) <- ask
    case exp of
        Spi v1 a1@(Sid t1 x1 y1) b1
            | Just (Spi v2 a2@(Sid t2 x2 y2) b2) <- isArr i a1 b1, Just (Sid t3 x3 y3) <- isArr i a2 b2
            , cmpTypes i t1 t2 && cmpTypes i t2 t3 && cmpValues i y1 x2 t1 && cmpValues i x1 x3 t1 && cmpValues i y2 y3 t2
            -> return exp
        _ -> errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
                etext "But comp has type of the form Id A x y -> Id A y z -> Id A x z"
typeOfH (Inv (PInv (lc,_))) (T exp) = do
    (i,c,_,_) <- ask
    case exp of
        Spi v a@(Sid t x y) b
            | Just (Sid t' x' y') <- isArr i a b, cmpTypes i t t' && cmpValues i x y' t && cmpValues i x' y t
            -> return exp
        _ -> errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But inv has type of the form Id A x y -> Id A y x"
-- invIdp : (p : Id t x y) -> Id (Id (Id t x y) p p) (comp (inv p) p) (idp p)
typeOfH e@(InvIdp _) (T exp@(Spi v a@(Sid t x y) b)) = do
    let ctx' = (M.fromList [("a",(a,Stype maxBound))], [])
        term = T.Pi [(["p"],T.Var "a")] $ T.Id
            (T.Id (T.Var "a") (T.LVar 0) (T.LVar 0))
            (T.Comp `T.App` (T.Inv `T.App` T.LVar 0) `T.App` T.LVar 0)
            (T.Idp `T.App` T.LVar 0)
    cmpTypesErr exp (eval 0 ctx' term) e
    return exp
typeOfH (InvIdp (PInvIdp (lc,_))) (T exp) = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But invIdp has type of the form Id A x y -> _"
typeOfH e (T exp) = do
    act <- typeOf e
    cmpTypesErr exp act e
    return exp

typeOfH (Pair e1 e2) N = liftTCM2' sprod (typeOf e1) (typeOf e2)
typeOfH (Lam (PLam (lc,_)) _ _) N = inferErrorMsg lc "the argument"
typeOfH (Idp (PIdp (lc,_))) N = inferErrorMsg lc "idp"
typeOfH (Coe (PCoe (lc,_))) N = inferErrorMsg lc "coe"
typeOfH (App e1 e) N | Idp _ <- dropParens e1 = do
    t <- typeOf e
    (i,_,mctx,ctx) <- ask
    let v = evalRaw i mctx ctx e (Just t)
    return (Sid t v v)
typeOfH (Pmap (Ppmap (lc,_))) N = inferErrorMsg lc "pmap"
typeOfH (Ext (PExt (lc,_))) N = inferErrorMsg lc "ext"
typeOfH (Proj1 (PProjl (lc,_))) N = inferErrorMsg lc "proj1"
typeOfH (Proj2 (PProjr (lc,_))) N = inferErrorMsg lc "proj2"
typeOfH (App e1 e) N | Proj1 _ <- dropParens e1 = do
    t <- typeOf e
    case t of
        Ssigma _ a _ -> return a
        _ -> expTypeBut "Sigma" e t
typeOfH (App e1 e) N | Proj2 (PProjr p) <- dropParens e1 = do
    t <- typeOf e
    case t of
        Ssigma _ a b -> do
            (i,_,mctx,ctx) <- ask
            return $ b 0 [] $ evalRaw i mctx ctx (App (Proj1 $ PProjl p) e) (Just a)
        _ -> expTypeBut "Sigma" e t
typeOfH (App e1 _) N | Pmap (Ppmap (lc,_)) <- dropParens e1 = inferErrorMsg lc "ext"
-- pmap (idp e1) e2
typeOfH (App e1' e2) N
    | App e3 e4 <- dropParens e1'
    , Pmap _ <- dropParens e3
    , App e5 e1 <- dropParens e4
    , Idp _ <- dropParens e5 = do
        t2 <- typeOf e2
        case t2 of
            Sid s a b -> typeOfH e1 (P e2 s a b)
            _ -> expTypeBut "Id" e2 t2
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfH (App e1' e2) N | App e3 e1 <- dropParens e1', Pmap _ <- dropParens e3 = do
    (t1,t2) <- liftTCM2' (,) (typeOf e1) (typeOf e2)
    case t1 of
        Sid t f g -> typeOfPmap t f g t2 e1 e2
        _ -> expTypeBut "Id" e1 t1
typeOfH (App e1 e) N | Coe _ <- dropParens e1 = do
    t <- typeOf e
    case t of
        Sid (Stype _) x y -> return (x `sarr` y)
        _ -> expTypeBut "Id Type _ _" e t
typeOfH (App e1 e) N | Inv _ <- dropParens e1 = do
    t <- typeOf e
    case t of
        Sid t' x y -> return (Sid t' y x)
        _ -> expTypeBut "Id" e t
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeOfH (App e1 e) N | InvIdp _ <- dropParens e1 = do
    t <- typeOf e
    case t of
        Sid _ _ _ -> do
            (i,_,mctx,ctx) <- ask
            let e' = evalRaw i mctx ctx e Nothing
            return $ Sid (Sid t e' e') (comp 0 (inv 0 e') e') (idp 0 e')
        _ -> expTypeBut "Id" e t
typeOfH (App e1' e2) N | App e3 e1 <- dropParens e1', Comp (PComp (lc,_)) <- dropParens e3 = do
    r <- liftTCM2' (,) (typeOf e1) (typeOf e2)
    (i,c,_,_) <- ask
    case r of
        (Sid t1 x1 y1, Sid t2 x2 y2) | cmpTypes i t1 t2 -> if cmpValues i y1 x2 t1
            then return (Sid t1 x1 y2)
            else errorTCM $ emsgLC lc "" $ etext "Terms" <+> epretty c (reify i y1 t1)
                 <+> etext "and" <+> epretty c (reify i x2 t2) <+> etext "must be equal"
        (Sid t1 _ _, Sid t2 _ _) -> errorTCM $ emsgLC lc "" $ etext "Types" <+> epretty c (reifyType i t1)
                                    <+> etext "and" <+> epretty c (reifyType i t2) <+> etext "must be equal"
        (Sid _ _ _, t2) -> expTypeBut "Id" e2 t2
        (t1, Sid _ _ _) -> expTypeBut "Id" e1 t1
        (t1, t2) -> liftTCM2' const (expTypeBut "Id" e1 t1) (expTypeBut "Id" e2 t2)
typeOfH (Arr e1 e2) N = liftTCM2 (maxType e1 e2) (typeOf e1) (typeOf e2)
typeOfH (Prod e1 e2) N = typeOf (Arr e1 e2)
typeOfH (Pi tv e) N = typeOf'depType tv e
typeOfH (Sigma tv e) N = typeOf'depType tv e
typeOfH (Id a b) N = do
    a' <- typeOf a
    typeOfH b (T a')
    (i,_,_,ctx) <- ask
    return $ typeOfTerm 0 ctx (reifyType i a')
typeOfH (Nat _) N = return $ Stype (Finite 0)
typeOfH (Universe (U (_,t))) N = return $ Stype $ succ (parseLevel t)
typeOfH (App e1 e2) N = do
    t1 <- typeOf e1
    case t1 of
        Spi _ a b -> do
            typeOfH e2 (T a)
            (i,_,mctx,ctx) <- ask
            return $ b 0 [] $ evalRaw i mctx ctx e2 (Just a)
        _ -> expTypeBut "pi" e1 t1
typeOfH (Var (NoArg (Pus (lc,_)))) N = errorTCM $ emsgLC lc "Expected identifier" enull
typeOfH (Var (Arg (PIdent (lc,x)))) N = do
    (i,_,mctx,(ctx,lctx)) <- ask
    case (M.lookup x mctx, M.lookup x ctx) of
        (Nothing, Nothing) -> errorTCM $ emsgLC lc ("Unknown identifier " ++ x) enull
        (Nothing, Just (_,t)) -> return t
        (Just l, _) -> return $ snd $ lctx `genericIndex` (i - l - 1)
typeOfH (Suc _) N = return (sarr Snat Snat)
typeOfH (NatConst _) N = return Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfH (Rec _) N = return $ eval 0 (M.empty,[]) $ T.Pi [(["P"], T.Pi [([],T.Nat)] $ T.Universe Omega)] $
    T.Pi [([], T.App (T.LVar 0) $ T.NatConst 0)] $ T.Pi [([], iht)] $ T.Pi [(["x"],T.Nat)] $ T.App (T.LVar 1) (T.LVar 0)
  where iht = T.Pi [(["x"],T.Nat)] $ T.Pi [([], T.App (T.LVar 1) (T.LVar 0))] $ T.App (T.LVar 1) $ T.App T.Suc (T.LVar 0)
typeOfH (Typed e t) N = do
    typeOfH t $ T (Stype maxBound)
    (i,_,mctx,ctx) <- ask
    typeOfH e $ T $ evalRaw i mctx ctx t $ Just (Stype maxBound)
typeOfH (Iso _) N =
    let term = T.Pi [(["A"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [(["B"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [(["f"],T.Pi [([],T.LVar 1)] $ T.LVar 0)] $
               T.Pi [(["g"],T.Pi [([],T.LVar 1)] $ T.LVar 2)] $
               T.Pi [([],T.Pi [(["a"],T.LVar 3)] $
                    T.Id (T.LVar 4) (T.LVar 1 `T.App` (T.LVar 2 `T.App` T.LVar 0)) (T.LVar 0))] $
               T.Pi [([],T.Pi [(["b"],T.LVar 2)] $
                    T.Id (T.LVar 3) (T.LVar 2 `T.App` (T.LVar 1 `T.App` T.LVar 0)) (T.LVar 0))] $
               T.Id (T.Universe $ pred $ pred maxBound) (T.LVar 3) (T.LVar 2)
    in return (eval 0 (M.empty,[]) term)
typeOfH (Comp (PComp (lc,_))) N = inferErrorMsg lc "comp"
typeOfH (Inv (PInv (lc,_))) N = inferErrorMsg lc "inv"
typeOfH (InvIdp (PInvIdp (lc,_))) N = inferErrorMsg lc "invIdp"

typeOfPmap :: Value -> Value -> Value -> Value -> Expr -> Expr -> TCM Value
typeOfPmap (Spi v a b) f g (Sid a' x y) _ e2 = do
    (i,c,mctx,ctx) <- ask
    if cmpTypes i a' a
        then return $ Sid (b 0 [] y) (trans 0 (Slam v b) (evalRaw i mctx ctx e2 Nothing) (app 0 f x)) (app 0 g y)
        else pmapErrMsg e2 a' (eprettyType i c a)
typeOfPmap t1 _ _ (Sid _ _ _) e1 _ = pmapErrMsg e1 t1 (etext "_ -> _")
typeOfPmap _ _ _ t2 _ e2 = expTypeBut "Id" e2 t2

isArr :: T.DBIndex -> Value -> (Integer -> [D] -> Value -> Value) -> Maybe Value
isArr i t f =
    let r = f 0 [] (svar i t)
    in if isFreeVar 0 (i + 1) r then Nothing else Just r

evalDecl :: String -> Expr -> Maybe Expr -> TCM (M.Map String T.DBIndex, Ctx, Value, Value)
evalDecl name expr mty = do
    (i,_,mctx,actx@(ctx,lctx)) <- ask
    tv <- case mty of
        Nothing -> typeOf expr
        Just ty -> do
            typeOfH ty $ T $ Stype (pred maxBound)
            let tv = evalRaw i mctx actx ty $ Just $ Stype (pred maxBound)
            typeOfH expr (T tv)
            return tv
    let ev = evalRaw i mctx actx expr (Just tv)
    return (M.delete name mctx, (M.insert name (ev,tv) ctx, lctx), ev, tv)

eprettyType :: T.DBIndex -> [String] -> Value -> EDoc
eprettyType i c t = epretty c $ T.simplify (reifyType i t)

inferErrorMsg :: (Int,Int) -> String -> TCM a
inferErrorMsg lc s = errorTCM $ emsgLC lc ("Cannot infer type of " ++ s) enull

pmapErrMsg :: Expr -> Value -> EDoc -> TCM a
pmapErrMsg expr ty j = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos expr) "" $ etext "Expected type of the form Id(" <> j <> etext ") _ _" $$
        etext "But term" <+> eprettyExpr expr <+> etext "has type Id(" <> eprettyType i c ty <> etext ") _ _"

coeErrorMsg :: (Int,Int) -> Value -> TCM a
coeErrorMsg lc ty = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c 1 ty $$ etext "But coe has type of the form Id Type A B -> A -> B"

pmapErrorMsg :: (Int,Int) -> Value -> TCM a
pmapErrorMsg lc ty = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) ty $$ etext ("But pmap has type of the form "
        ++ "Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)")

pmap1ErrorMsg :: (Int,Int) -> Value -> TCM a
pmap1ErrorMsg lc ty = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) ty $$
        etext "But pmap _ has type of the form (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)"

proj1ErrorMsg :: (Int,Int) -> Value -> TCM a
proj1ErrorMsg lc exp = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$ etext "But proj1 has type of the form ((a : A) -> B a) -> A"

proj2ErrorMsg :: (Int,Int) -> Value -> TCM a
proj2ErrorMsg lc exp = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
        etext "But proj2 has type of the form (p : (a : A) -> B a) -> B (proj1 p)"

extErrorMsg :: (Int,Int) -> Value -> TCM a
extErrorMsg lc exp = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC lc "" $ expType i c (-1) exp $$
        etext ("But ext has type either of the form ((x : A) -> f x = g x) -> f = g or "
        ++ "of the form (s : Id A a a') * Id (B a') (trans B s b) b' -> Id ((a : A) * B a) (a,b) (a',b')")

expType :: T.DBIndex -> [String] -> Int -> Value -> EDoc
expType i c l ty = etext "Expected type:" <+> eprettyLevel c l (T.simplify $ reifyType i ty)

cmpTypesErr :: Value -> Value -> Expr -> TCM ()
cmpTypesErr t1 t2 e = do
    (i,c,_,_) <- ask
    if cmpTypes i t2 t1
        then return ()
        else errorTCM $ emsgLC (getPos e) "" $ expType i c (-1) t1 $$
            etext "But term" <+> eprettyExpr e <+> etext "has type" <+> eprettyType i c t2

expTypeBut :: String -> Expr -> Value -> TCM a
expTypeBut exp e act = do
    (i,c,_,_) <- ask
    errorTCM $ emsgLC (getPos e) "" $ etext ("Expected " ++ exp ++ " type") $$
        etext "But term" <+> eprettyExpr e <+> etext "has type" <+> eprettyHead c (T.simplify $ reifyType i act)
