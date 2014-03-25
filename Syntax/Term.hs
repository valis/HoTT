module Syntax.Term
    ( Term(..), Def(..), DBIndex
    , ppTerm, ppDef
    , freeVars, liftTermDB
    , simplify, simplifyDef
    ) where

import qualified Data.Map as M
import Text.PrettyPrint
import Data.List
import Syntax.Common

data Def = Def String (Maybe (Term,[String])) Term

type DBIndex = Integer

data Term
    = Let [Def] Term
    | Lam [String] Term
    | Pi [([String],Term)] Term
    | Sigma [([String],Term)] Term
    | Id Term Term Term
    | App Term Term
    | NoVar
    | Var String
    | LVar DBIndex
    | Nat
    | Suc
    | Rec
    | Idp
    | Pmap
    | Coe
    | Proj1
    | Proj2
    | Iso
    | Comp
    | Inv
    | InvIdp
    | NatConst Integer
    | Universe Level
    | Typed Term Term
    | Ext Term Term
    | ExtSigma Term Term
    | Pair Term Term

infixl 5 `App`

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
freeVars (Ext e1 e2) = freeVars e1 `union` freeVars e2
freeVars (ExtSigma e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Pair e1 e2) = freeVars e1 `union` freeVars e2
freeVars NoVar = []
freeVars (Var v) = [v]
freeVars (LVar _) = []
freeVars Nat = []
freeVars Suc = []
freeVars Rec = []
freeVars Idp = []
freeVars Pmap = []
freeVars Coe = []
freeVars Proj1 = []
freeVars Proj2 = []
freeVars Iso = []
freeVars Comp = []
freeVars Inv = []
freeVars InvIdp = []
freeVars (NatConst _) = []
freeVars (Universe _) = []
freeVars (Typed e1 e2) = freeVars e1 `union` freeVars e2

liftTermDB :: DBIndex -> Term -> Term
liftTermDB = go 0
  where
    go n k (Let defs e) = Let (map (goDef n k) defs) e
    go n k (Lam vars e) = Lam vars $ go (genericLength vars + n) k e
    go n k (Pi vars e) =
        let (v,l) = goVars n k vars
        in Pi v (go l k e)
    go n k (Sigma vars e) =
        let (v,l) = goVars n k vars
        in Sigma v (go l k e)
    go n k (Id t e1 e2) = Id (go n k t) (go n k e1) (go n k e2)
    go n k (App e1 e2) = App (go n k e1) (go n k e2)
    go n k (Ext e1 e2) = Ext (go n k e1) (go n k e2)
    go n k (ExtSigma e1 e2) = ExtSigma (go n k e1) (go n k e2)
    go n k (Pair e1 e2) = Pair (go n k e1) (go n k e2)
    go _ _ NoVar = NoVar
    go _ _ e@(Var _) = e
    go n k (LVar i) | i < n = LVar i
                    | otherwise = LVar (i + k)
    go _ _ Nat = Nat
    go _ _ Suc = Suc
    go _ _ Rec = Rec
    go _ _ Idp = Idp
    go _ _ Pmap = Pmap
    go _ _ Coe = Coe
    go _ _ Proj1 = Proj1
    go _ _ Proj2 = Proj2
    go _ _ Iso = Iso
    go _ _ Comp = Comp
    go _ _ Inv = Inv
    go _ _ InvIdp = InvIdp
    go _ _ e@(NatConst _) = e
    go _ _ e@(Universe _) = e
    go n k (Typed e1 e2) = Typed (go n k e1) (go n k e2)
    
    goVars n k [] = ([], n)
    goVars n k ((vars,t):vs) =
        let (r, n') = goVars (n + genericLength vars) k vs
        in ((vars, go n k t) : r, n')
    
    goDef n k (Def name Nothing expr) = Def name Nothing (go n k expr)
    goDef n k (Def name (Just (ty, args)) expr) = Def name (Just (go n k ty, args)) $ go (n + genericLength args) k expr

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
        cmp c m1 m2 (Let (Def v1 (Just (t1,_)) r1 : ds1) e1) (Let (Def v2 (Just (t2,_)) r2 : ds2) e2) =
            cmp c m1 m2 t1 t2 && cmp c m1 m2 r1 r2 &&
            cmp (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) (Let ds1 e1) (Let ds2 e2)
        cmp c m1 m2 (Lam (_:vs1) e1) (Lam (_:vs2) e2) = cmp c m1 m2 (Lam vs1 e1) (Lam vs2 e2)
        cmp c m1 m2 (Pi ((_,t1):ts1) e1) (Pi ((_,t2):ts2) e2) =
            cmp c m1 m2 t1 t2 && cmp c m1 m2 (Pi ts1 e1) (Pi ts2 e2)
        cmp c m1 m2 (Sigma ((_,t1):ts1) e1) (Sigma ((_,t2):ts2) e2) =
            cmp c m1 m2 t1 t2 && cmp c m1 m2 (Sigma ts1 e1) (Sigma ts2 e2)
        cmp c m1 m2 (Id t1 a1 b1) (Id t2 a2 b2) = cmp c m1 m2 t1 t2 && cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (App a1 b1) (App a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Typed a1 b1) (Typed a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Ext a1 b1) (Ext a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (ExtSigma a1 b1) (ExtSigma a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Pair a1 b1) (Pair a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (LVar v1) (LVar v2) = v1 == v2
        cmp c m1 m2 (Var v1) (Var v2) = M.lookup v1 m1 == M.lookup v2 m2
        cmp _ _ _ NoVar NoVar = True
        cmp _ _ _ Nat Nat = True
        cmp _ _ _ Suc Suc = True
        cmp _ _ _ Rec Rec = True
        cmp _ _ _ Idp Idp = True
        cmp _ _ _ Pmap Pmap = True
        cmp _ _ _ Coe Coe = True
        cmp _ _ _ Proj1 Proj1 = True
        cmp _ _ _ Proj2 Proj2 = True
        cmp _ _ _ Iso Iso = True
        cmp _ _ _ Comp Comp = True
        cmp _ _ _ Inv Inv = True
        cmp _ _ _ InvIdp InvIdp = True
        cmp _ _ _ (NatConst c1) (NatConst c2) = c1 == c2
        cmp _ _ _ (Universe l1) (Universe l2) = l1 == l2
        cmp _ _ _ _ _ = False

ppDef :: [String] -> Def -> Doc
ppDef ctx (Def name Nothing          expr) = text name <+> equals <+> ppTerm ctx Nothing expr
ppDef ctx (Def name (Just (ty,args)) expr) = text name <+> colon  <+> ppTerm ctx Nothing ty
    $+$ text name <+> hsep (map text args) <+> equals <+> ppTerm (reverse args ++ ctx) Nothing expr

ppTerm :: [String] -> Maybe Int -> Term -> Doc
ppTerm ctx = go ctx False
  where
    ppArrow ctx l e@(Lam _ _) = go ctx True l e
    ppArrow ctx l e@(Pi _ _) = go ctx True l e
    ppArrow ctx l e = go ctx False l e
    
    isComp (Let _ _) = True
    isComp (Lam _ _) = True
    isComp (Pi _ _) = True
    isComp (Sigma _ _) = True
    isComp (Id _ _ _) = True
    isComp _ = False
    
    ppId ctx l e@(Lam _ _) = go ctx True l e
    ppId ctx l e@(Pi _ _) = go ctx True l e
    ppId ctx l e@(Id _ _ _) = go ctx True l e
    ppId ctx l e = go ctx False l e
    
    ppVars :: [String] -> Bool -> Char -> Maybe Int -> [([String],Term)] -> Doc
    ppVars _ _ c l [] = char c
    ppVars ctx True c l ts = char c <+> ppVars ctx False c l ts
    ppVars ctx False c l (([],t):ts) =
        let l' = fmap pred l
        in ppArrow ctx l' t <+> ppVars ctx True c l' ts
    ppVars ctx False c l ((vars,t):ts) =
        let l' = fmap pred l
            b = not (null ts) && null (fst $ head ts)
        in parens (hsep (map text vars) <+> colon <+> go ctx False l' t) <+> ppVars ctx b c l' ts
    
    go :: [String] -> Bool -> Maybe Int -> Term -> Doc
    go _ _ (Just 0) _ = char '_'
    go _ _ _ (NatConst n) = integer n
    go _ _ _ x | Just n <- getNat x = integer n
      where
        getNat :: Term -> Maybe Integer
        getNat (NatConst n) = Just n
        getNat (App Suc x) = fmap succ (getNat x)
        getNat _ = Nothing
    go _ _ _ NoVar = text "_"
    go _ _ _ (Var v) = text v
    go ctx _ _ (LVar v) = text (ctx `genericIndex` v)
    go _ _ _ Nat = text "Nat"
    go _ _ _ Suc = text "suc"
    go _ _ _ Rec = text "R"
    go _ _ _ Idp = text "idp"
    go _ _ _ (Ext _ _) = text "ext"
    go _ _ _ (ExtSigma _ _) = text "ext"
    go _ _ _ Pmap = text "pmap"
    go _ _ _ Coe = text "coe"
    go _ _ _ Proj1 = text "proj1"
    go _ _ _ Proj2 = text "proj2"
    go _ _ _ Iso = text "iso"
    go _ _ _ Comp = text "comp"
    go _ _ _ Inv = text "inv"
    go _ _ _ InvIdp = text "invIdp"
    go _ _ _ (Universe u) = text (show u)
    go ctx True l e = parens (go ctx False l e)
    go ctx False l (Let defs e) = text "let" <+> vcat (map (ppDef ctx) defs) $+$ text "in" <+> go ctx False l e
    go ctx False l (Lam vars e) = char 'λ' <> hsep (map text vars) <+>
        char '→' <+> go (reverse vars ++ ctx) False (fmap pred l) e
    go ctx False l (Pi ts e) =
        let l' = fmap pred l
        in ppVars ctx False '→' l' ts <+> go ctx False l' e
    go ctx False l (Sigma ts e) =
        let l' = fmap pred l
        in ppVars ctx False '×' l' ts <+> ppArrow ctx l' e
    go ctx False l (Id _ e1 e2) =
        let l' = fmap pred l
        in ppId ctx l' e1 <+> equals <+> ppId ctx l' e2
    go ctx False l (App e1 e2) =
        let l' = fmap pred l
        in go ctx False l' e1 <+> go ctx True l' e2
    go ctx False l (Typed e1 e2) =
        let l' = fmap pred l
        in go ctx (isComp e1) l' e1 <+> text "::" <+> go ctx False l' e2
    go ctx False l (Pair e1 e2) =
        let l' = fmap pred l
        in go ctx False l' e1 <+> comma <+> go ctx False l' e2

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
simplify (Typed e1 e2) = Typed (simplify e1) (simplify e2)
simplify (Pair e1 e2) = Pair (simplify e1) (simplify e2)
simplify e@(Ext _ _) = e
simplify e@(ExtSigma _ _) = e
simplify e@(Var _) = e
simplify e@(LVar _) = e
simplify NoVar = NoVar
simplify Nat = Nat
simplify Suc = Suc
simplify Rec = Rec
simplify Idp = Idp
simplify Pmap = Pmap
simplify Coe = Coe
simplify Proj1 = Proj1
simplify Proj2 = Proj2
simplify Iso = Iso
simplify Comp = Comp
simplify Inv = Inv
simplify InvIdp = InvIdp
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
