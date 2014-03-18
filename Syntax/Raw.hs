module Syntax.Raw
    ( unArg, unBinder
    , getPos, argGetPos, binderGetPos
    , freeVars, renameExpr
    , preprocessDefs
    ) where

import Data.List
import Text.PrettyPrint

import Parser.AbsGrammar
import ErrorDoc hiding ((<+>),(<>),($$))
import Syntax.Common

getPos :: Expr -> (Int,Int)
getPos (Let [] e) = getPos e
getPos (Let (Def (PIdent (p,_)) _ _ : _) _) = p
getPos (Let (DefType (PIdent (p,_)) _ : _) _) = p
getPos (Lam (PLam (p,_)) _ _) = p
getPos (Arr e _) = getPos e
getPos (Prod e _) = getPos e
getPos (Pi [] e) = getPos e
getPos (Pi (TypedVar (PPar (p,_)) _ _ : _) _) = p
getPos (Sigma [] e) = getPos e
getPos (Sigma (TypedVar (PPar (p,_)) _ _ : _) _) = p
getPos (Id e _) = getPos e
getPos (App e _) = getPos e
getPos (Var (NoArg (Pus (p,_)))) = p
getPos (Var (Arg (PIdent (p,_)))) = p
getPos (Nat (PNat (p,_))) = p
getPos (Suc (PSuc (p,_))) = p
getPos (Rec (PR (p,_))) = p
getPos (Idp (PIdp (p,_))) = p
getPos (Ext (PExt (p,_))) = p
getPos (Pmap (Ppmap (p,_))) = p
getPos (Trans (PTrans (p,_))) = p
getPos (NatConst (PInt (p,_))) = p
getPos (Universe (U (p,_))) = p
getPos (Paren (PPar (p,_)) _) = p
getPos (Typed e _) = getPos e
getPos (Pair e _) = getPos e
getPos (Proj1 (PProjl (lc,_))) = lc
getPos (Proj2 (PProjr (lc,_))) = lc

unArg :: Arg -> String
unArg (NoArg _) = "_"
unArg (Arg (PIdent (_,x))) = x

argGetPos :: Arg -> (Int,Int)
argGetPos (NoArg (Pus (p,_))) = p
argGetPos (Arg (PIdent (p,_))) = p

unBinder :: Binder -> String
unBinder (Binder b) = unArg b

binderGetPos :: Binder -> (Int,Int)
binderGetPos (Binder b) = argGetPos b

freeVarsDef :: [Def] -> Expr -> [String]
freeVarsDef [] e = freeVars e
freeVarsDef (DefType _ t : ds) e = freeVars t `union` freeVarsDef ds e
freeVarsDef (Def (PIdent (_,x)) as t : ds) e = (freeVars t \\ map unArg as) `union` delete x (freeVarsDef ds e)

freeVars :: Expr -> [String]
freeVars (Let defs e) = freeVarsDef defs e
freeVars (Lam _ bnds e) = freeVars e \\ map unBinder bnds
freeVars (Arr e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pi [] e) = freeVars e
freeVars (Pi (TypedVar _ vars t : xs) e) = freeVars t `union` (freeVars (Pi xs e) \\ freeVars vars)
freeVars (Prod e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Sigma [] e) = freeVars e
freeVars (Sigma (TypedVar _ vars t : xs) e) = freeVars t `union` (freeVars (Sigma xs e) \\ freeVars vars)
freeVars (Id e1 e2) = freeVars e1 `union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pair e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var (Arg (PIdent (_,x)))) = [x]
freeVars (Var (NoArg _)) = []
freeVars (Nat _) = []
freeVars (Suc _) = []
freeVars (Rec _) = []
freeVars (Idp _) = []
freeVars (Ext _) = []
freeVars (Pmap _) = []
freeVars (Trans _) = []
freeVars (Proj1 _) = []
freeVars (Proj2 _) = []
freeVars (NatConst _) = []
freeVars (Universe _) = []
freeVars (Paren _ e) = freeVars e
freeVars (Typed e1 e2) = freeVars e1 `union` freeVars e2

renameExpr :: [String] -> String -> Expr -> (String,Expr)
renameExpr m x e | not (elem x m) = (x,e)
                 | otherwise = let x' = freshName x (m ++ freeVars e) in (x', rename e x x')

renameDefs :: [Def] -> Expr -> String -> String -> ([Def],Expr)
renameDefs [] e x y = ([], rename e x y)
renameDefs r@(DefType (PIdent (i,z)) t : defs) e x y
    | z == x = (r,e)
    | z == y =
        let (y', e1') = renameExpr [z,x] y (Let defs e)
            (defs1,e1) = case e1' of { Let defs1 e1 -> (defs1,e1); _ -> error "Raw.renameDefs.1" }
            (defs2, e2) = renameDefs defs1 e1 x y
        in (DefType (PIdent (i,y')) (rename t x y) : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
        in (DefType (PIdent (i,z)) (rename t x y) : defs', e')
renameDefs r@(Def (PIdent (i,z)) as t : defs) e x y
    | z == x = (r,e)
    | z == y =
        let (y', e1') = renameExpr [z,x] y (Let defs e)
            (defs1,e1) = case e1' of { Let defs1 e1 -> (defs1,e1); _ -> error "Raw.renameDefs.2" }
            (defs2, e2) = renameDefs defs1 e1 x y
            t2 = rename (Lam (error "renameDefs.==") (map Binder as) t) x y
            (as',t') = case t2 of { Lam _ as' t' -> (as',t'); _ -> error "Raw.renameDefs.3" }
        in (Def (PIdent (i,y')) (map (\(Binder a) -> a) as') t' : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
            t2 = rename (Lam (error "renameDefs./=") (map Binder as) t) x y
            (as',t') = case t2 of { Lam _ as' t' -> (as',t'); _ -> error "Raw.renameDefs.4" }
        in (Def (PIdent (i,z)) (map (\(Binder a) -> a) as') t' : defs', e')

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename (Let defs e) x y = let (defs',e') = renameDefs defs e x y in Let defs' e'
rename e@(Lam i bs e1) x y
    | elem x bs' = e
    | elem y bs' = Lam i (map (\y1 -> if unBinder y1 == y then renameBinder y1 y' else y1) bs) (rename e' x y)
    | otherwise = Lam i bs (rename e1 x y)
  where
    bs' = map unBinder bs
    (y',e') = renameExpr (x:bs') y e1
    renameBinder :: Binder -> String -> Binder
    renameBinder b@(Binder (NoArg _)) _ = b
    renameBinder (Binder (Arg (PIdent (i,_)))) x = Binder $ Arg $ PIdent (i,x)
rename (Arr e1 e2) x y = Arr (rename e1 x y) (rename e2 x y)
rename (Pi [] e) x y = rename e x y
rename (Pi (TypedVar p (Var (Arg (PIdent (i,z)))) t : bs) e) x y | x == z
    = Pi [TypedVar p (Var (Arg (PIdent (i,z)))) (rename t x y)] (Pi bs e)
rename (Pi (TypedVar p v t : bs) e) x y = Pi [TypedVar p v (rename t x y)] $ rename (Pi bs e) x y
rename (Prod e1 e2) x y = Prod (rename e1 x y) (rename e2 x y)
rename (Sigma [] e) x y = rename e x y
rename (Sigma (TypedVar p (Var (Arg (PIdent (i,z)))) t : bs) e) x y | x == z
    = Sigma [TypedVar p (Var (Arg (PIdent (i,z)))) (rename t x y)] (Sigma bs e)
rename (Sigma (TypedVar p v t : bs) e) x y = Sigma [TypedVar p v (rename t x y)] $ rename (Sigma bs e) x y
rename (Id e1 e2) x y = Id (rename e1 x y) (rename e2 x y)
rename (App e1 e2) x y = App (rename e1 x y) (rename e2 x y)
rename (Pair e1 e2) x y = Pair (rename e1 x y) (rename e2 x y)
rename (Var (Arg (PIdent (i,z)))) x y | x == z = Var $ Arg $ PIdent (i,y)
rename e@(Var _) _ _ = e
rename e@(Nat _) _ _ = e
rename e@(Suc _) _ _ = e
rename e@(Rec _) _ _ = e
rename e@(Idp _) _ _ = e
rename e@(Ext _) _ _ = e
rename e@(Pmap _) _ _ = e
rename e@(Trans _) _ _ = e
rename e@(Proj1 _) _ _ = e
rename e@(Proj2 _) _ _ = e
rename e@(NatConst _) _ _ = e
rename e@(Universe _) _ _ = e
rename (Paren i e) x y = Paren i (rename e x y)
rename (Typed e1 e2) x y = Typed (rename e1 x y) (rename e2 x y)

instance EPretty Expr where
    epretty = edoc . ppExpr Nothing

ppDef :: Def -> Doc
ppDef (Def (PIdent (_,name)) args expr) = text name <+> hsep (map (text . unArg) args) <+> equals <+> ppExpr Nothing expr 
ppDef (DefType (PIdent (_,name)) expr) = text name <+> colon <+> ppExpr Nothing expr

ppExpr :: Maybe Int -> Expr -> Doc
ppExpr = go False
  where
    ppArrow l e@(Lam _ _ _) = go True l e
    ppArrow l e@(Pi _ _) = go True l e
    ppArrow l e = go False l e
    
    isComp (Let _ _) = True
    isComp (Lam _ _ _) = True
    isComp (Pi _ _) = True
    isComp (Sigma _ _) = True
    isComp (Arr _ _) = True
    isComp (Prod _ _) = True
    isComp (Id _ _) = True
    isComp _ = False
    
    go _ (Just 0) _ = char '_'
    go _ _ (NatConst (PInt (_,n))) = text n
    go _ _ x | Just n <- getNat x = integer n
      where
        getNat :: Expr -> Maybe Integer
        getNat (NatConst (PInt (_,n))) = Just (read n)
        getNat (App (Suc _) x) = fmap succ (getNat x)
        getNat _ = Nothing
    go _ _ (Var a) = text (unArg a)
    go _ _ (Nat _) = text "Nat"
    go _ _ (Suc _) = text "suc"
    go _ _ (Rec _) = text "R"
    go _ _ (Idp _) = text "idp"
    go _ _ (Ext _) = text "ext"
    go _ _ (Pmap _) = text "pmap"
    go _ _ (Trans _) = text "trans"
    go _ _ (Proj1 _) = text "proj1"
    go _ _ (Proj2 _) = text "proj2"
    go _ _ (Universe (U (_,u))) = text u
    go True l e = parens (go False l e)
    go False l (Let defs e) = text "let" <+> vcat (map ppDef defs) $+$ text "in" <+> go False l e
    go False l (Lam _ vars e) = char 'λ' <> hsep (map (text . unBinder) vars) <+> char '→' <+> go False (fmap pred l) e
    go False l (Pi ts e) =
        let l' = fmap pred l
            ppTypedVar (TypedVar _ e t) = parens $ go False Nothing e <+> colon <+> go False l' t
        in hsep (map ppTypedVar ts) <+> char '→' <+> go False l' e
    go False l (Sigma ts e) =
        let l' = fmap pred l
            ppTypedVar (TypedVar _ e t) = parens $ go False Nothing e <+> colon <+> go False l' t
        in hsep (map ppTypedVar ts) <+> char '×' <+> go False l' e
    go False l (Arr e1 e2) =
        let l' = fmap pred l
        in ppArrow l' e1 <+> char '→' <+> go False l' e2
    go False l (Prod e1 e2) =
        let l' = fmap pred l
        in ppArrow l' e1 <+> char '×' <+> ppArrow l' e2
    go False l (Id e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> equals <+> go False l' e2
    go False l (App e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> go True l' e2
    go False l (Paren _ e) = go False l e
    go False l (Typed e1 e2) =
        let l' = fmap pred l
        in go (isComp e1) l' e1 <+> text "::" <+> go False l' e2
    go False l (Pair e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> comma <+> go False l' e2

preprocessDefs :: [Def] -> EDocM [Def]
preprocessDefs defs =
    let typeSigs = filterTypeSigs defs
        funDecls = filterFunDecls defs
        typeSigs' = map (\(PIdent (_,s),e) -> (s,e)) typeSigs
        typeSigsDup = duplicates (map fst typeSigs)
        funDeclsDup = duplicates (map fst funDecls)
    in if not (null typeSigsDup) || not (null funDeclsDup)
        then Left $ map (\(PIdent ((l,c),s)) -> emsgLC l c ("Duplicate type signatures for " ++ s) enull) typeSigsDup
                 ++ map (\(PIdent ((l,c),s)) -> emsgLC l c ("Multiple declarations of " ++ s) enull) funDeclsDup
        else fmap concat $ forE funDecls $ \(i@(PIdent ((l,c),name)),(args,expr)) -> case lookup name typeSigs' of
            Nothing -> if null args
                then Right [Def i [] expr]
                else Left [emsgLC l c "Cannot infer type of the argument" enull]
            Just ty -> Right [DefType i ty, Def i args expr]
  where
    filterTypeSigs :: [Def] -> [(PIdent,Expr)]
    filterTypeSigs [] = []
    filterTypeSigs (DefType x e : defs) = (x,e) : filterTypeSigs defs
    filterTypeSigs (_:defs) = filterTypeSigs defs
    
    filterFunDecls :: [Def] -> [(PIdent,([Arg],Expr))]
    filterFunDecls [] = []
    filterFunDecls (Def x a e : defs) = (x,(a,e)) : filterFunDecls defs
    filterFunDecls (_:defs) = filterFunDecls defs
    
    duplicates :: [PIdent] -> [PIdent]
    duplicates [] = []
    duplicates (x@(PIdent (_,v)) : xs) = case findRemove xs of
        Nothing -> duplicates xs
        Just xs' -> x : duplicates xs'
      where
        findRemove :: [PIdent] -> Maybe [PIdent]
        findRemove [] = Nothing
        findRemove (y@(PIdent (_,w)) : ys)
            | v == w = Just $ maybe ys id (findRemove ys)
            | otherwise = fmap (y:) (findRemove ys)
