module Syntax.Term
    ( Term(..), Def(..)
    , ppTerm, ppDef
    , freeVars
    , simplify, simplifyDef
    ) where

import qualified Data.Map as M
import Text.PrettyPrint
import Data.List
import Syntax.Common

data Def = Def String (Maybe (Term,[String])) Term

data Term
    = Let [Def] Term
    | Lam [String] Term
    | Pi [([String],Term)] Term
    | Sigma [([String],Term)] Term
    | Id Term Term Term
    | App Term Term
    | Var String
    | Nat
    | Suc
    | Rec
    | Idp
    | Trans
    | NatConst Integer
    | Universe Level

freeVars :: Term -> [String]
freeVars (Let defs e) = freeVars e \\ map (\(Def name _ _) -> name) defs
freeVars (Lam [] e) = freeVars e
freeVars (Lam (v:vs) e) = delete v $ freeVars (Lam vs e)
freeVars (Pi [] e) = freeVars e
freeVars (Pi ((vars,t):vs) e) = freeVars t `union` (freeVars (Pi vs e) \\ vars)
freeVars (Sigma [] e) = freeVars e
freeVars (Sigma ((vars,t):vs) e) = freeVars t `union` (freeVars (Sigma vs e) \\ vars)
freeVars (Id t e1 e2) = freeVars t `union` freeVars e1 `union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var "_") = []
freeVars (Var v) = [v]
freeVars Nat = []
freeVars Suc = []
freeVars Rec = []
freeVars Idp = []
freeVars Trans = []
freeVars (NatConst _) = []
freeVars (Universe _) = []

instance Eq Term where
    (==) = cmp 0 M.empty M.empty
      where
        cmp :: Int -> M.Map String Int -> M.Map String Int -> Term -> Term -> Bool
        cmp c m1 m2 (Let [] e1) e2 = cmp c m1 m2 e1 e2
        cmp c m1 m2 e1 (Let [] e2) = cmp c m1 m2 e1 e2
        cmp c m1 m2 (Lam [] e1) e2 = cmp c m1 m2 e1 e2
        cmp c m1 m2 e1 (Lam [] e2) = cmp c m1 m2 e1 e2
        cmp c m1 m2 (Pi [] e1) e2 = cmp c m1 m2 e1 e2
        cmp c m1 m2 e1 (Pi [] e2) = cmp c m1 m2 e1 e2
        cmp c m1 m2 (Sigma [] e1) e2 = cmp c m1 m2 e1 e2
        cmp c m1 m2 e1 (Sigma [] e2) = cmp c m1 m2 e1 e2
        cmp c m1 m2 (Sigma (([],_):ts) e1) e2 = cmp c m1 m2 (Sigma ts e1) e2
        cmp c m1 m2 e1 (Sigma (([],_):ts) e2) = cmp c m1 m2 e1 (Sigma ts e2)
        cmp c m1 m2 (Let (Def v1 Nothing r1 : ds1) e1) (Let (Def v2 Nothing r2 : ds2) e2) =
            cmp c m1 m2 r1 r2 && cmp (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) (Let ds1 e1) (Let ds2 e2)
        cmp c m1 m2 (Let (Def v1 (Just (t1,as1)) r1 : ds1) e1) (Let (Def v2 (Just (t2,as2)) r2 : ds2) e2) =
            cmp c m1 m2 t1 t2 &&
            cmpVars c m1 m2 as1 as2 r1 r2 &&
            cmp (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) (Let ds1 e1) (Let ds2 e2)
        cmp c m1 m2 (Lam (v1:vs1) e1) (Lam (v2:vs2) e2) =
            cmp (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) (Lam vs1 e1) (Lam vs2 e2)
        cmp c m1 m2 (Pi ((vs1,t1):ts1) e1) (Pi ((vs2,t2):ts2) e2) =
            cmp c m1 m2 t1 t2 && cmpVars c m1 m2 vs1 vs2 (Pi ts1 e1) (Pi ts2 e2)
        cmp c m1 m2 (Sigma ((vs1,t1):ts1) e1) (Sigma ((vs2,t2):ts2) e2) =
            cmp c m1 m2 t1 t2 && cmpVars c m1 m2 vs1 vs2 (Sigma ts1 e1) (Sigma ts2 e2)
        cmp c m1 m2 (Id t1 a1 b1) (Id t2 a2 b2) = cmp c m1 m2 t1 t2 && cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (App a1 b1) (App a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Var v1) (Var v2) = case (M.lookup v1 m1, M.lookup v2 m2) of
            (Nothing, Nothing) -> v1 == v2
            (Just c1, Just c2) -> c1 == c2
            _ -> False
        cmp _ _ _ Nat Nat = True
        cmp _ _ _ Suc Suc = True
        cmp _ _ _ Rec Rec = True
        cmp _ _ _ Idp Idp = True
        cmp _ _ _ Trans Trans = True
        cmp _ _ _ (NatConst c1) (NatConst c2) = c1 == c2
        cmp _ _ _ (Universe l1) (Universe l2) = l1 == l2
        cmp _ _ _ _ _ = False
        
        cmpVars c m1 m2 [] [] e1 e2 = cmp c m1 m2 e1 e2
        cmpVars c m1 m2 (v1:vs1) (v2:vs2) e1 e2 = cmpVars (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) vs1 vs2 e1 e2
        cmpVars _ _ _ _ _ _ _ = False

ppDef :: Def -> Doc
ppDef (Def name Nothing          expr) = text name <+> equals <+> ppTerm Nothing expr
ppDef (Def name (Just (ty,args)) expr) = text name <+> colon  <+> ppTerm Nothing ty
                                     $+$ text name <+> hsep (map text args) <+> equals <+> ppTerm Nothing expr

ppTerm :: Maybe Int -> Term -> Doc
ppTerm = go False
  where
    ppArrow l e@(Lam _ _) = go True l e
    ppArrow l e@(Pi _ _) = go True l e
    ppArrow l e = go False l e
    
    ppId l e@(Lam _ _) = go True l e
    ppId l e@(Pi _ _) = go True l e
    ppId l e@(Id _ _ _) = go True l e
    ppId l e = go False l e
    
    ppVars :: Bool -> Char -> Maybe Int -> [([String],Term)] -> Doc
    ppVars _ c l [] = char c
    ppVars True c l ts = char c <+> ppVars False c l ts
    ppVars False c l (([],t):ts) =
        let l' = fmap pred l
        in ppArrow l' t <+> ppVars True c l' ts
    ppVars False c l ((vars,t):ts) =
        let l' = fmap pred l
            b = not (null ts) && null (fst $ head ts)
        in parens (hsep (map text vars) <+> colon <+> go False l' t) <+> ppVars b c l' ts
    
    go _ (Just 0) _ = char '_'
    go _ _ (NatConst n) = integer n
    go _ _ x | Just n <- getNat x = integer n
      where
        getNat :: Term -> Maybe Integer
        getNat (NatConst n) = Just n
        getNat (App Suc x) = fmap succ (getNat x)
        getNat _ = Nothing
    go _ _ (Var v) = text v
    go _ _ Nat = text "Nat"
    go _ _ Suc = text "suc"
    go _ _ Rec = text "R"
    go _ _ Idp = text "idp"
    go _ _ Trans = text "trans"
    go _ _ (Universe u) = text (show u)
    go True l e = parens (go False l e)
    go False l (Let defs e) = text "let" <+> vcat (map ppDef defs) $+$ text "in" <+> go False l e
    go False l (Lam vars e) = char 'λ' <> hsep (map text vars) <+> char '→' <+> go False (fmap pred l) e
    go False l (Pi ts e) =
        let l' = fmap pred l
        in ppVars False '→' l' ts <+> go False l' e
    go False l (Sigma ts e) =
        let l' = fmap pred l
        in ppVars False '×' l' ts <+> ppArrow l' e
    go False l (Id _ e1 e2) =
        let l' = fmap pred l
        in ppId l' e1 <+> equals <+> ppId l' e2
    go False l (App e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> go True l' e2

simplify :: Term -> Term
simplify (Let [] e) = simplify e
simplify (Let defs (Let defs' e)) = simplify $ Let (defs ++ defs') e
simplify (Let defs e) = Let (map simplifyDef defs) (simplify e)
simplify (Lam [] e) = simplify e
simplify (Lam args (Lam args' e)) = simplify $ Lam (args ++ args') e
simplify (Lam args e) = Lam (simplifyArgs args $ args \\ freeVars e) (simplify e)
  where
    simplifyArgs args [] = args
    simplifyArgs [] _ = []
    simplifyArgs (a:as) (r:rs) | a == r = "_" : simplifyArgs as rs
                               | otherwise = a : simplifyArgs as (r:rs)
simplify (Pi [] e) = simplify e
simplify (Pi (([],t):ts) e) = Pi [([], simplify t)] $ simplify (Pi ts e)
simplify (Pi (([v],t):ts) e)
    | elem v (freeVars $ Pi ts e) = case simplify (Pi ts e) of
        Pi ts' e' -> Pi (([v], simplify t):ts') e'
        r -> Pi [([v], simplify t)] r
    | otherwise = case simplify (Pi ts e) of
        Pi ts' e' -> Pi (([], simplify t):ts') e'
        r -> Pi [([], simplify t)] r
simplify (Pi ((v:vs,t):ts) e)
    | elem v (freeVars $ Pi ((vs,t):ts) e) = case simplify $ Pi ((vs,t):ts) e of
        Pi ts' e' -> Pi (([v], simplify t):ts') e'
        r -> Pi [([v], simplify t)] r
    | otherwise = Pi [([], simplify t)] $ simplify (Pi ((vs,t):ts) e)
simplify (Sigma [] e) = simplify e
simplify (Sigma (([],t):ts) e) = Sigma [([], simplify t)] $ simplify (Sigma ts e)
simplify (Sigma (([v],t):ts) e)
    | elem v (freeVars $ Sigma ts e) = case simplify (Sigma ts e) of
        Sigma ts' e' -> Sigma (([v], simplify t):ts') e'
        r -> Sigma [([v], simplify t)] r
    | otherwise = case simplify (Sigma ts e) of
        Sigma ts' e' -> Sigma (([], simplify t):ts') e'
        r -> Sigma [([], simplify t)] r
simplify (Sigma ((v:vs,t):ts) e)
    | elem v (freeVars $ Sigma ((vs,t):ts) e) = case simplify $ Sigma ((vs,t):ts) e of
        Sigma ts' e' -> Sigma (([v], simplify t):ts') e'
        r -> Sigma [([v], simplify t)] r
    | otherwise = Sigma [([], simplify t)] $ simplify (Sigma ((vs,t):ts) e)
simplify (Id t a b) = Id (simplify t) (simplify a) (simplify b)
simplify (App e1 e2) = App (simplify e1) (simplify e2)
simplify e@(Var _) = e
simplify Nat = Nat
simplify Suc = Suc
simplify Rec = Rec
simplify Idp = Idp
simplify Trans = Trans
simplify e@(NatConst _) = e
simplify e@(Universe _) = e

simplifyDef :: Def -> Def
simplifyDef (Def name Nothing expr) = Def name Nothing (simplify expr)
simplifyDef (Def name (Just (ty,args)) expr) =
    let (args',expr') = extractArgs (simplify expr)
    in Def name (Just (simplify ty, args ++ args')) expr'
  where
    extractArgs :: Term -> ([String],Term)
    extractArgs (Lam xs e) = let (ys,r) = extractArgs e in (xs ++ ys, r)
    extractArgs e = ([],e)
