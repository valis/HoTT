module Syntax.Raw
    ( unArg, unBinder
    , getPos, argGetPos, binderGetPos
    , dropParens
    , preprocessDefs
    , eprettyExpr
    ) where

import Text.PrettyPrint

import Parser.AbsGrammar
import ErrorDoc hiding ((<+>),(<>),($$))
import Syntax.Common()

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
getPos (Over e _) = getPos e
getPos (App e _) = getPos e
getPos (Var (NoArg (Pus (p,_)))) = p
getPos (Var (Arg (PIdent (p,_)))) = p
getPos (Nat (PNat (p,_))) = p
getPos (Suc (PSuc (p,_))) = p
getPos (Rec (PR (p,_))) = p
getPos (Idp (PIdp (p,_))) = p
getPos (Ext (PExt (p,_))) = p
getPos (Pmap (Ppmap (p,_))) = p
getPos (Coe (PCoe (p,_))) = p
getPos (NatConst (PInt (p,_))) = p
getPos (Universe (U (p,_))) = p
getPos (Paren (PPar (p,_)) _) = p
getPos (Pair e _) = getPos e
getPos (Proj1 (PProjl (lc,_))) = lc
getPos (Proj2 (PProjr (lc,_))) = lc
getPos (Iso (PIso (lc,_))) = lc
getPos (Comp (PComp (lc,_))) = lc
getPos (Inv (PInv (lc,_))) = lc
getPos (InvIdp (PInvIdp (lc,_))) = lc

dropParens :: Expr -> Expr
dropParens (Paren _ e) = dropParens e
dropParens e = e

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

eprettyExpr :: Expr -> EDoc
eprettyExpr = edoc . ppExpr Nothing

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
    go _ _ (Coe _) = text "coe"
    go _ _ (Proj1 _) = text "proj1"
    go _ _ (Proj2 _) = text "proj2"
    go _ _ (Iso _) = text "iso"
    go _ _ (Comp _) = text "comp"
    go _ _ (Inv _) = text "inv"
    go _ _ (InvIdp _) = text "invIdp"
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
    go False l (Over e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> char '|' <+> go False l' e2
    go False l (App e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> go True l' e2
    go False l (Paren _ e) = go False l e
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
        then Left $ map (\(PIdent (lc,s)) -> emsgLC lc ("Duplicate type signatures for " ++ s) enull) typeSigsDup
                 ++ map (\(PIdent (lc,s)) -> emsgLC lc ("Multiple declarations of " ++ s) enull) funDeclsDup
        else fmap concat $ forE funDecls $ \(i@(PIdent (lc,name)),(args,expr)) -> case lookup name typeSigs' of
            Nothing -> if null args
                then Right [Def i [] expr]
                else Left [emsgLC lc "Cannot infer type of the argument" enull]
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
