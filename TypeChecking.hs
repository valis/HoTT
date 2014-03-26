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

maxType :: T.DBIndex -> Expr -> Expr -> Value -> Value -> EDocM Value
maxType _ _ _ (Stype k1) (Stype k2) = Right $ Stype (max k1 k2)
maxType i e1 e2 t1 t2 = liftErr2 (error "maxType")
    (cmpTypesErr i (Stype $ pred maxBound) t1 e1)
    (cmpTypesErr i (Stype $ pred maxBound) t2 e2)

processDefs :: [Def] -> [(String,Maybe Expr,[Arg],Expr)]
processDefs [] = []
processDefs (DefType _ t : Def (PIdent (_,name)) args e : defs) = (name,Just t,args,e) : processDefs defs
processDefs (Def (PIdent (_,name)) args e : defs) = (name,Nothing,args,e) : processDefs defs
processDefs _ = error "processDefs"

typeOf'depType :: T.DBIndex -> M.Map String T.DBIndex -> Ctx -> [TypedVar] -> Expr -> EDocM Value
typeOf'depType i mctx ctx [] e = typeOf i mctx ctx e
typeOf'depType i mctx actx@(ctx,lctx) (TypedVar _ vars t : list) e = do
    tv <- typeOf i mctx actx t
    let e' = Pi list e
    cmpTypesErr i (Stype $ pred maxBound) tv t
    (mctx',lctx',i') <- updateCtx i mctx lctx (evalRaw i mctx actx t (Just tv)) vars
    ev <- typeOf i' mctx' (ctx,lctx') e'
    maxType i' t e' tv ev
  where
    updateCtx i mctx lctx _ (Var (NoArg _)) = Right (mctx,lctx,i)
    updateCtx i mctx lctx tv (Var (Arg (PIdent (_,x)))) = Right (M.insert x i mctx, (svar i tv,tv) : lctx, i + 1)
    updateCtx i mctx lctx tv (App a (Var (NoArg _))) = updateCtx i mctx lctx tv a
    updateCtx i mctx lctx tv (App a (Var (Arg (PIdent (_,x))))) =
        updateCtx (i + 1) (M.insert x i mctx) ((svar i tv, tv) : lctx) tv a
    updateCtx _ _ _ _ e = Left [emsgLC (getPos e) "Expected identifier" enull]

dropParens :: Expr -> Expr
dropParens (Paren _ e) = dropParens e
dropParens e = e

data H = P Expr Value Value Value | T Value | N

typeOf :: T.DBIndex -> M.Map String T.DBIndex -> Ctx -> Expr -> EDocM Value
typeOf i mctx ctx e = typeOfH i mctx ctx e N

typeOfH :: T.DBIndex -> M.Map String T.DBIndex -> Ctx -> Expr -> H -> EDocM Value
typeOfH i mctx ctx (Let defs e) h = do
    defs' <- preprocessDefs defs
    let st = forM_ (processDefs defs') $ \(name,ty,args,expr) ->
            let p = if null args then getPos expr else argGetPos (head args)
            in evalDecl i mctx name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    ctx' <- execStateT st ctx
    typeOfH i mctx ctx' e h
typeOfH i mctx ctx (Paren _ e) h = typeOfH i mctx ctx e h
typeOfH i mctx ctx (Lam _ [] e) h = typeOfH i mctx ctx e h

typeOfH i mctx (ctx,lctx) e1@(Lam (PLam (lc,_)) (x:xs) e) (P _ ty a b) = do
    let p = if null xs then getPos e else binderGetPos (head xs)
        e' = Lam (PLam (p,"\\")) xs e
    s <- typeOf (i + 1) (M.insert (unBinder x) i mctx) (ctx, (svar i ty,ty) : lctx) e'
    if isFreeVar i s
        then inferErrorMsg lc "lambda expression"
        else let v1 = evalRaw i mctx (ctx,lctx) e1 $ Just (ty `sarr` s)
             in Right $ Sid s (app 0 v1 a) (app 0 v1 b)
typeOfH i mctx ctx e1 (P e2 act a b) = do
    t1 <- typeOf i mctx ctx e1
    let v1 = evalRaw i mctx ctx e1 Nothing
    typeOfPmap i mctx ctx t1 v1 v1 (Sid act a b) e1 e2

typeOfH i mctx (ctx,lctx) (Lam _ (x:xs) e) (T r@(Spi z a b)) = do
    let p = if null xs then getPos e else binderGetPos (head xs)
        v = svar i a
    typeOfH (i + 1) (M.insert (unBinder x) i mctx) (ctx, (v,a) : lctx) (Lam (PLam (p,"\\")) xs e) (T (b 0 [] v))
    return r
typeOfH i mctx _ (Lam _ (Binder arg : _) _) (T ty) =
    let lc = case arg of
            Arg (PIdent (p,_)) -> p
            NoArg (Pus (p,_)) -> p
    in Left [emsgLC lc "" $ expType i 1 ty $$ etext "But lambda expression has pi type"]
typeOfH i _ _ j@(Idp _) (T exp@(Spi x a _)) = do
    let ctx = (M.singleton (freshName "a" [x]) a, [])
    cmpTypesErr i exp (eval 0 ctx $ T.Pi [([x],T.Var "a")] $ T.Id (T.Var "a") (T.Var x) (T.Var x)) j
    return exp
typeOfH i mctx _ (Idp (PIdp (lc,_))) (T ty) =
    Left [emsgLC lc "" $ expType i 1 ty $$ etext "But idp has pi type"]
typeOfH i mctx ctx e@(Coe (PCoe (lc,_))) (T ty@(Spi v a@(Sid (Stype _) x y) b)) = case b 0 [] $ svar i a of
    Spi v' x' y' -> if cmpTypes i x x' && cmpTypes (i + 1) y (y' 0 [] $ svar i x') -- ???
        then return ty
        else coeErrorMsg i lc ty
    _ -> coeErrorMsg i lc ty
typeOfH i mctx ctx (Coe (PCoe (lc,_))) (T ty) = coeErrorMsg i lc ty
typeOfH i mctx ctx ea@(App e1 e) (T exp@(Sid t a b)) | Idp _ <- dropParens e1 = do
    typeOfH i mctx ctx e (T t)
    let e' = evalRaw i mctx ctx e (Just t)
    cmpTypesErr i exp (Sid t e' e') ea
    return exp
typeOfH i mctx ctx (App e1 _) (T exp) | Idp (PIdp (lc,_)) <- dropParens e1 =
    Left [emsgLC lc "" $ expType i 1 exp $$ etext "But idp _ has Id type"]
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfH i mctx ctx e@(Pmap (Ppmap (lc,_))) (T exp@(Spi v a@(Sid (Spi v' a' b') f g) b)) =
    case isArr i a b of
        Just (Spi v2 a2'@(Sid a2 x y) b2') | cmpTypes i a2 a' ->
            let ctx' = [("a",a),("a'",a'),("x",x),("y",y),("B",Slam v' b'),("f'",app 0 f x),("g'",app 0 g y)]
                term = T.Pi [([],T.Var "a")] $ T.Pi [(["p"],T.Id (T.Var "a'") (T.Var "x") (T.Var "y"))] $
                    T.Id (T.Var "B" `T.App` T.Var "y")
                         (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.Var "p") `T.App` T.Var "f'")
                         (T.Var "g'")
            in cmpTypesErr i exp (eval 0 (M.fromList ctx', []) term) e >> return exp
        _ -> pmapErrorMsg i lc exp
typeOfH i mctx ctx (Pmap (Ppmap (lc,_))) (T exp) = pmapErrorMsg i lc exp
typeOfH i mctx ctx ea@(App e1 e) (T ty@(Spi v a'@(Sid a x y) b')) | Pmap _ <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    case t of
        Sid (Spi v1 a1 b1) f g | cmpTypes i a a1 -> do
            let ctx' = [("a'",a'),("B",Slam v1 b1),("y",y),("f'",app 0 f x),("g'",app 0 g y)]
                term = T.Pi [(["p"],T.Var "a'")] $ T.Id (T.Var "B" `T.App` T.Var "y")
                    (T.Coe `T.App` (T.Pmap `T.App` (T.Idp `T.App` T.Var "B") `T.App` T.Var "p") `T.App` T.Var "f'")
                    (T.Var "g'")
            cmpTypesErr i ty (eval 0 (M.fromList ctx', []) term) ea
            return ty
        _ -> Left [emsgLC (getPos e) "" $ etext "Expected type: Id(" <+> epretty (T.Pi [([],reifyType i a)] $ T.Var "_")
                <+> etext ") _ _" $$ etext "But term" <+> epretty e <+> etext "has type" <+> epretty (reifyType i t)]
typeOfH i mctx ctx (App e1 e) (T ty) | Pmap (Ppmap (lc,_)) <- dropParens e1 = pmap1ErrorMsg i lc ty
typeOfH i mctx ctx (Ext (PExt (lc,_))) (T ty@(Spi x' s@(Spi _ a' b') t)) = case isArr i s t of
    Just (Sid (Spi _ a b) f g) | cmpTypes i a a' ->
        let v = svar i a
        in if cmpTypes (i + 1) (b' 0 [] v) (Sid (b 0 [] v) (app 0 f v) (app 0 g v)) then Right ty else extErrorMsg i lc ty
    _ -> extErrorMsg i lc ty
-- ext : (s : Id A x x') * Id (B x') (trans B s y) y' -> Id ((x : A) * B x) (x,y) (x',y')
--       a'              * b'                         -> Id (a       * b  ) p     q
typeOfH i mctx ctx (Ext (PExt (lc,_))) (T ty@(Spi x' s@(Ssigma _ a' b') t)) = case isArr i s t of
    Just (Sid (Ssigma x a b) p q) ->
        let v = svar i $ Sid a (proj1 p) (proj1 q)
        in if cmpTypes i a' (Sid a (proj1 p) (proj1 q)) &&
              cmpTypes (i + 1) (b' 0 [] v) (Sid (b 0 [] $ proj1 q) (trans 0 (Slam x b) s $ proj2 p) (proj2 q))
           then Right ty
           else extErrorMsg i lc ty
    _ -> extErrorMsg i lc ty
typeOfH i mctx ctx (Ext (PExt (lc,_))) (T ty) = extErrorMsg i lc ty
typeOfH i mctx ctx (App e1 e) (T r@(Sid (Spi x a b) f g)) | Ext _ <- dropParens e1 = do
    typeOfH i mctx ctx e $ T $ Spi x a $ \k m v -> Sid (b k m v) (app k (action m f) v) (app k (action m g) v)
    return r
-- (s : Id a (proj1 p) (proj1 q)) * (Id (B (proj1 q)) (trans B s (proj2 p)) (proj2 q))
typeOfH i mctx ctx (App e1 e) (T r@(Sid (Ssigma x a b) p q)) | Ext _ <- dropParens e1 = do
    typeOfH i mctx ctx e $ T $ Ssigma x (Sid a (proj1 p) (proj1 q)) $ \k m s ->
        let r1 = action m $ b 0 [] (proj1 q)
            r2 = trans k (action m $ Slam x b) s $ action m (proj2 p)
            r3 = action m (proj2 q)
        in eval k (M.fromList [("r1",r1),("r2",r2),("r3",r3)], []) $ T.Id (T.Var "r1") (T.Var "r2") (T.Var "r3")
    return r
typeOfH i mctx ctx (App e1 e) (T exp) | Ext (PExt (lc,_)) <- dropParens e1 = Left [emsgLC lc "" $ expType i (-1) exp $$
    etext "But term ext _ has type either of the form Id ((x : A) -> B x) _ _ or of the form Id ((x : A) * B x) _ _"]
typeOfH i mctx ctx (App e1 e) (T exp@(Sid t x y)) | Inv _ <- dropParens e1 = do
    typeOfH i mctx ctx e $ T (Sid t y x)
    return exp
typeOfH i mctx ctx (App e1 e) (T exp) | Inv (PInv (lc,_)) <- dropParens e1 =
    Left [emsgLC lc "" $ expType i (-1) exp $$ etext "But term inv _ has Id type"]
typeOfH i mctx ctx (Pair e1 e2) (T r@(Ssigma _ a b)) = do
    typeOfH i mctx ctx e1 (T a)
    typeOfH i mctx ctx e2 $ T $ b 0 [] $ evalRaw i mctx ctx e1 (Just a)
    return r
typeOfH i mctx ctx e@(Pair _ _) (T exp) =
    Left [emsgLC (getPos e) "" $ expType i (-1) exp $$ etext "But term" <+> epretty e <+> etext "has Sigma type"]
typeOfH i mctx ctx (Proj1 (PProjl (lc,_))) (T r@(Spi x a'@(Ssigma _ a _) b)) = case isArr i a' b of
    Just b' | cmpTypes i a b' -> Right r
    _ -> proj1ErrorMsg i lc r
typeOfH i mctx ctx (Proj1 (PProjl (lc,_))) (T exp) = proj1ErrorMsg i lc exp
-- proj2 : (p : (x : A) -> B x) -> B (proj1 p)
typeOfH i mctx ctx (Proj2 (PProjr (lc,_))) (T r@(Spi x a'@(Ssigma _ a b) b')) =
    if cmpTypes (i + 1) (b 0 [] $ liftTerm (\l -> T.App T.Proj1 $ T.LVar $ l - i - 1) a) (b' 0 [] $ svar i a')
        then Right r
        else proj2ErrorMsg i lc r
typeOfH i mctx ctx (Proj2 (PProjr (lc,_))) (T exp) = proj2ErrorMsg i lc exp
typeOfH i mctx ctx (Comp _) (T exp@(Spi v1 a1@(Sid t1 x1 y1) b1))
    | Just (Spi v2 a2@(Sid t2 x2 y2) b2) <- isArr i a1 b1, Just (Sid t3 x3 y3) <- isArr i a2 b2
    , cmpTypes i t1 t2 && cmpTypes i t2 t3 && cmpValues i y1 x2 t1 && cmpValues i x1 x3 t1 && cmpValues i y2 y3 t2
    = Right exp
typeOfH i mctx ctx (Comp (PComp (lc,_))) (T exp) = Left [emsgLC lc "" $ expType i (-1) exp $$
    etext "But comp has type of the form Id A x y -> Id A y z -> Id A x z"]
typeOfH i mctx ctx (Inv _) (T exp@(Spi v a@(Sid t x y) b))
    | Just (Sid t' x' y') <- isArr i a b, cmpTypes i t t' && cmpValues i x y' t && cmpValues i x' y t = Right exp
typeOfH i mctx ctx (Inv (PInv (lc,_))) (T exp) = Left [emsgLC lc "" $ expType i (-1) exp $$
    etext "But inv has type of the form Id A x y -> Id A y x"]
-- invIdp : (p : Id t x y) -> Id (Id (Id t x y) p p) (comp (inv p) p) (idp p)
typeOfH i mctx ctx e@(InvIdp _) (T exp@(Spi v a@(Sid t x y) b)) =
    let ctx' = (M.fromList [("a",a)], [])
        term = T.Pi [(["p"],T.Var "a")] $ T.Id
            (T.Id (T.Var "a") (T.Var "p") (T.Var "p"))
            (T.Comp `T.App` (T.Inv `T.App` T.Var "p") `T.App` T.Var "p")
            (T.Idp `T.App` T.Var "p")
    in do cmpTypesErr i exp (eval 0 ctx' term) e
          return exp
typeOfH i mctx ctx (InvIdp (PInvIdp (lc,_))) (T exp) = Left [emsgLC lc "" $ expType i (-1) exp $$
    etext "But invIdp has type of the form Id A x y -> _"]
typeOfH i mctx ctx e (T exp) = do
    act <- typeOf i mctx ctx e
    cmpTypesErr i exp act e
    return exp

typeOfH i mctx ctx (Pair e1 e2) N = liftErr2' sprod (typeOf i mctx ctx e1) (typeOf i mctx ctx e2)
typeOfH i mctx _ (Lam (PLam (lc,_)) _ _) N = inferErrorMsg lc "the argument"
typeOfH i mctx _ (Idp (PIdp (lc,_))) N = inferErrorMsg lc "idp"
typeOfH i mctx _ (Coe (PCoe (lc,_))) N = inferErrorMsg lc "coe"
typeOfH i mctx ctx (App e1 e) N | Idp _ <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    let v = evalRaw i mctx ctx e (Just t)
    Right (Sid t v v)
typeOfH i mctx _ (Pmap (Ppmap (lc,_))) N = inferErrorMsg lc "pmap"
typeOfH i mctx ctx (Ext (PExt (lc,_))) N = inferErrorMsg lc "ext"
typeOfH i mctx _ (Proj1 (PProjl (lc,_))) N = inferErrorMsg lc "proj1"
typeOfH i mctx _ (Proj2 (PProjr (lc,_))) N = inferErrorMsg lc "proj2"
typeOfH i mctx ctx (App e1 e) N | Proj1 _ <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    case t of
        Ssigma _ a _ -> Right a
        _ -> expTypeBut i "Sigma" e t
typeOfH i mctx ctx (App e1 e) N | Proj2 (PProjr p) <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    case t of
        Ssigma _ a b -> Right $ b 0 [] $ evalRaw i mctx ctx (App (Proj1 $ PProjl p) e) (Just a)
        _ -> expTypeBut i "Sigma" e t
typeOfH i mctx _ (App e1 _) N | Pmap (Ppmap (lc,_)) <- dropParens e1 = inferErrorMsg lc "ext"
-- pmap (idp e1) e2
typeOfH i mctx ctx (App e1' e2) N
    | App e3 e4 <- dropParens e1'
    , Pmap _ <- dropParens e3
    , App e5 e1 <- dropParens e4
    , Idp _ <- dropParens e5 = do
        t2 <- typeOf i mctx ctx e2
        case t2 of
            Sid s a b -> typeOfH i mctx ctx e1 (P e2 s a b)
            _ -> expTypeBut i "Id" e2 t2
-- pmap : Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (trans B p (f x)) (g y)
typeOfH i mctx ctx (App e1' e2) N | App e3 e1 <- dropParens e1', Pmap _ <- dropParens e3 = do
    (t1,t2) <- liftErr2' (,) (typeOf i mctx ctx e1) (typeOf i mctx ctx e2)
    case t1 of
        Sid t f g -> typeOfPmap i mctx ctx t f g t2 e1 e2
        _ -> expTypeBut i "Id" e1 t1
typeOfH i mctx ctx (App e1 e) N | Coe _ <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    case t of
        Sid (Stype _) x y -> Right (x `sarr` y)
        _ -> expTypeBut i "Id Type _ _" e t
typeOfH i mctx ctx (App e1 e) N | Inv _ <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    case t of
        Sid t' x y -> Right (Sid t' y x)
        _ -> expTypeBut i "Id" e t
-- invIdp (e : Id t x y) : Id (Id (Id t x y) e e) (comp (inv e) e) (idp e)
typeOfH i mctx ctx (App e1 e) N | InvIdp _ <- dropParens e1 = do
    t <- typeOf i mctx ctx e
    case t of
        Sid _ _ _ ->
            let e' = evalRaw i mctx ctx e Nothing
            in Right $ Sid (Sid t e' e') (comp 0 (inv 0 e') e') (idp e')
        _ -> expTypeBut i "Id" e t
typeOfH i mctx ctx (App e1' e2) N | App e3 e1 <- dropParens e1', Comp (PComp (lc,_)) <- dropParens e3 = do
    r <- liftErr2' (,) (typeOf i mctx ctx e1) (typeOf i mctx ctx e2)
    case r of
        (Sid t1 x1 y1, Sid t2 x2 y2) | cmpTypes i t1 t2 -> if cmpValues i y1 x2 t1
            then Right (Sid t1 x1 y2)
            else Left [emsgLC lc "" $ etext "Terms" <+> epretty (reify i y1 t1)
                <+> etext "and" <+> epretty (reify i x2 t2) <+> etext "must be equal"]
        (Sid t1 _ _, Sid t2 _ _) -> Left [emsgLC lc "" $ etext "Types" <+> epretty (reifyType i t1)
                <+> etext "and" <+> epretty (reifyType i t2) <+> etext "must be equal"]
        (Sid _ _ _, t2) -> expTypeBut i "Id" e2 t2
        (t1, Sid _ _ _) -> expTypeBut i "Id" e1 t1
        (t1, t2) -> liftErr2' const (expTypeBut i "Id" e1 t1) (expTypeBut i "Id" e2 t2)
typeOfH i mctx ctx (Arr e1 e2) N = liftErr2 (maxType i e1 e2) (typeOf i mctx ctx e1) (typeOf i mctx ctx e2)
typeOfH i mctx ctx (Prod e1 e2) N = typeOf i mctx ctx (Arr e1 e2)
typeOfH i mctx ctx (Pi tv e) N = typeOf'depType i mctx ctx tv e
typeOfH i mctx ctx (Sigma tv e) N = typeOf'depType i mctx ctx tv e
typeOfH i mctx ctx (Id a b) N = do
    a' <- typeOf i mctx ctx a
    typeOfH i mctx ctx b (T a')
    return $ typeOfTerm i ctx (reifyType i a')
typeOfH i mctx _ (Nat _) N = Right $ Stype (Finite 0)
typeOfH i mctx _ (Universe (U (_,t))) N = Right $ Stype $ succ (parseLevel t)
typeOfH i mctx ctx (App e1 e2) N = do
    t1 <- typeOf i mctx ctx e1
    case t1 of
        Spi _ a b -> do
            typeOfH i mctx ctx e2 (T a)
            return $ b 0 [] $ evalRaw i mctx ctx e2 (Just a)
        _ -> expTypeBut i "pi" e1 t1
typeOfH i mctx _ (Var (NoArg (Pus (lc,_)))) N = Left [emsgLC lc "Expected identifier" enull]
typeOfH i mctx (ctx,lctx) (Var (Arg (PIdent (lc,x)))) N = case (M.lookup x mctx, M.lookup x ctx) of
    (Nothing, Nothing) -> Left [emsgLC lc ("Unknown identifier " ++ x) enull]
    (Nothing, Just (_,t)) -> Right t
    (Just l, _) -> Right $ snd $ lctx `genericIndex` (i - l - 1)
typeOfH i mctx _ (Suc _) N = Right (sarr Snat Snat)
typeOfH i mctx _ (NatConst _) N = Right Snat
-- Rec : (P : Nat -> Type) -> P 0 -> ((x : Nat) -> P x -> P (Suc x)) -> (x : Nat) -> P x
typeOfH i mctx _ (Rec _) N = Right $ eval 0 (M.empty,[]) $ T.Pi [(["P"], T.Pi [([],T.Nat)] $ T.Universe Omega)] $
    T.Pi [([], T.App (T.Var "P") $ T.NatConst 0)] $ T.Pi [([], iht)] $ T.Pi [(["x"],T.Nat)] $ T.App (T.Var "P") (T.Var "x")
  where iht = T.Pi [(["x"],T.Nat)] $ T.Pi [([], T.App (T.Var "P") (T.Var "x"))] $ T.App (T.Var "P") $ T.App T.Suc (T.Var "x")
typeOfH i mctx ctx (Typed e t) N = do
    typeOfH i mctx ctx t $ T (Stype maxBound)
    typeOfH i mctx ctx e $ T $ evalRaw i mctx ctx t $ Just (Stype maxBound)
typeOfH i mctx ctx (Iso _) N =
    let term = T.Pi [(["A"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [(["B"],T.Universe $ pred $ pred maxBound)] $
               T.Pi [([],T.Pi [([],T.Var "A")] $ T.Var "B")] $
               T.Pi [([],T.Pi [([],T.Var "B")] $ T.Var "A")] $
               T.Pi [([],T.Pi [(["a"],T.Var "A")] $
                    T.Id (T.Var "A") (T.Var "g" `T.App` (T.Var "f" `T.App` T.Var "a")) (T.Var "a"))] $
               T.Pi [([],T.Pi [(["b"],T.Var "B")] $
                    T.Id (T.Var "B") (T.Var "f" `T.App` (T.Var "g" `T.App` T.Var "b")) (T.Var "b"))] $
               T.Id (T.Universe $ pred $ pred maxBound) (T.Var "A") (T.Var "B")
    in Right (eval 0 (M.empty,[]) term)
typeOfH i mctx ctx (Comp (PComp (lc,_))) N = inferErrorMsg lc "comp"
typeOfH i mctx ctx (Inv (PInv (lc,_))) N = inferErrorMsg lc "inv"
typeOfH i mctx ctx (InvIdp (PInvIdp (lc,_))) N = inferErrorMsg lc "invIdp"

typeOfPmap :: T.DBIndex -> M.Map String T.DBIndex -> Ctx -> Value -> Value -> Value -> Value -> Expr -> Expr -> EDocM Value
typeOfPmap i mctx ctx (Spi v a b) f g (Sid a' x y) _ e2
    | cmpTypes i a' a = Right $ Sid (b 0 [] y) (trans 0 (Slam v b) (evalRaw i mctx ctx e2 Nothing) (app 0 f x)) (app 0 g y)
    | otherwise = pmapErrMsg i e2 a' (eprettyType i a)
typeOfPmap i _ _ t1 _ _ (Sid _ _ _) e1 _ = pmapErrMsg i e1 t1 (etext "_ -> _")
typeOfPmap i _ _ _ _ _ t2 _ e2 = expTypeBut i "Id" e2 t2

isArr :: T.DBIndex -> Value -> (Integer -> [D] -> Value -> Value) -> Maybe Value
isArr i t f =
    let r = f 0 [] (svar i t)
    in if isFreeVar i r then Nothing else Just r

evalDecl :: T.DBIndex -> M.Map String T.DBIndex -> String -> Expr -> Maybe Expr -> StateT Ctx EDocM (Value,Value)
evalDecl i mctx name expr mty = do
    actx@(ctx,lctx) <- get
    tv <- case mty of
        Nothing -> lift (typeOf i mctx actx expr)
        Just ty -> do
            lift $ typeOfH i mctx actx ty $ T $ Stype (pred maxBound)
            let tv = evalRaw i mctx actx ty $ Just $ Stype (pred maxBound)
            lift $ typeOfH i mctx actx expr (T tv)
            return tv
    let ev = evalRaw i mctx actx expr (Just tv)
    put (M.insert name (ev,tv) ctx, lctx)
    return (ev,tv)

eprettyType :: T.DBIndex -> Value -> EDoc
eprettyType i t = epretty $ T.simplify (reifyType i t)

inferErrorMsg :: (Int,Int) -> String -> EDocM a
inferErrorMsg lc s = Left [emsgLC lc ("Cannot infer type of " ++ s) enull]

pmapErrMsg :: T.DBIndex -> Expr -> Value -> EDoc -> EDocM a
pmapErrMsg i expr ty j =
    Left [emsgLC (getPos expr) "" $ etext "Expected type of the form Id(" <> j <> etext ") _ _" $$
        etext "But term" <+> epretty expr <+> etext "has type Id(" <> eprettyType i ty <> etext ") _ _"]

coeErrorMsg :: T.DBIndex -> (Int,Int) -> Value -> EDocM a
coeErrorMsg i lc ty = Left [emsgLC lc "" $ expType i 1 ty $$ etext "But coe has type of the form Id Type A B -> A -> B"]

pmapErrorMsg :: T.DBIndex -> (Int,Int) -> Value -> EDocM a
pmapErrorMsg i lc ty = Left [emsgLC lc "" $ expType i (-1) ty $$ etext ("But pmap has type of the form "
    ++ "Id ((a : A) -> B a) f g -> (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)")]

pmap1ErrorMsg :: T.DBIndex -> (Int,Int) -> Value -> EDocM a
pmap1ErrorMsg i lc ty = Left [emsgLC lc "" $ expType i (-1) ty $$
    etext "But pmap _ has type of the form (p : Id A x y) -> Id (B y) (coe (pmap (idp B) p) (f x)) (g y)"]

proj1ErrorMsg :: T.DBIndex -> (Int,Int) -> Value -> EDocM a
proj1ErrorMsg i lc exp = Left [emsgLC lc "" $ expType i (-1) exp $$
    etext "But proj1 has type of the form ((a : A) -> B a) -> A"]

proj2ErrorMsg :: T.DBIndex -> (Int,Int) -> Value -> EDocM a
proj2ErrorMsg i lc exp = Left [emsgLC lc "" $ expType i (-1) exp $$
    etext "But proj2 has type of the form (p : (a : A) -> B a) -> B (proj1 p)"]

extErrorMsg :: T.DBIndex -> (Int,Int) -> Value -> EDocM a
extErrorMsg i lc exp = Left [emsgLC lc "" $ expType i (-1) exp
    $$ etext ("But ext has type either of the form ((x : A) -> f x = g x) -> f = g or "
    ++ "of the form (s : Id A a a') * Id (B a') (trans B s b) b' -> Id ((a : A) * B a) (a,b) (a',b')")]

expType :: T.DBIndex -> Int -> Value -> EDoc
expType i l ty = etext "Expected type:" <+> eprettyLevel l (T.simplify $ reifyType i ty)

cmpTypesErr :: T.DBIndex -> Value -> Value -> Expr -> EDocM ()
cmpTypesErr i t1 t2 e = if cmpTypes i t2 t1
    then Right ()
    else Left [emsgLC (getPos e) "" $ expType i (-1) t1 $$
        etext "But term" <+> epretty e <+> etext "has type" <+> eprettyType i t2]

expTypeBut :: T.DBIndex -> String -> Expr -> Value -> EDocM a
expTypeBut i exp e act = Left [emsgLC (getPos e) "" $ etext ("Expected " ++ exp ++ " type") $$
    etext "But term" <+> epretty e <+> etext "has type" <+> eprettyHead (T.simplify $ reifyType i act)]
