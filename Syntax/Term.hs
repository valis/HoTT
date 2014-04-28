module Syntax.Term
    ( Term(..), Def(..)
    , DBIndex, ITerm
    , ppTerm, ppDef
    , freeLVars, liftTermDB
    , simplify, simplifyDef
    ) where

import qualified Data.Map as M
import Text.PrettyPrint
import Data.List
import Control.Arrow(first,second)

import Syntax.Common
import Cube

data Def = Def String (Maybe (Term,[String])) Term

type DBIndex = Integer
type ITerm = DBIndex -> Term

data Term
    = Let [Def] Term
    | Lam Integer [String] Term
    | Pi Integer [([String],Term)] Term
    | Sigma Integer [([String],Term)] Term
    | Id Integer Term Term Term
    | App Integer Term Term
    | NoVar
    | Var String
    | LVar DBIndex
    | Nat
    | Suc
    | Rec
    | Idp
    | Pmap Term Term
    | Coe
    | Proj1
    | Proj2
    | Iso
    | Pcon
    | NatConst Integer
    | Universe Level
    | Pair Term Term
    | Act CubeMap Term
    | Comp Integer Term Term
    | Inv Integer Term
    | Fibr Bool Integer Term Term

freeLVarsDef :: Def -> [DBIndex]
freeLVarsDef (Def _ Nothing e) = freeLVars e
freeLVarsDef (Def _ (Just (t,args)) e) = freeLVars t `union` map (\l -> l - genericLength args) (freeLVars e)

freeLVars :: Term -> [DBIndex]
freeLVars (Let defs e) = freeLVars e `union` concat (map freeLVarsDef defs)
freeLVars (Lam _ [] e) = freeLVars e
freeLVars (Lam n (v:vs) e) = map pred $ freeLVars (Lam n vs e)
freeLVars (Pi _ vs e) = freeLVarsDep vs e
freeLVars (Sigma _ vs e) = freeLVarsDep vs e
freeLVars (Id _ t e1 e2) = freeLVars t `union` freeLVars e1 `union` freeLVars e2
freeLVars (App _ e1 e2) = freeLVars e1 `union` freeLVars e2
freeLVars (Pair e1 e2) = freeLVars e1 `union` freeLVars e2
freeLVars NoVar = []
freeLVars (Var _) = []
freeLVars (LVar i) = [i]
freeLVars Nat = []
freeLVars Suc = []
freeLVars Rec = []
freeLVars Idp = []
freeLVars (Pmap e1 e2) = freeLVars e1 `union` freeLVars e2
freeLVars Coe = []
freeLVars Proj1 = []
freeLVars Proj2 = []
freeLVars Iso = []
freeLVars Pcon = []
freeLVars (NatConst _) = []
freeLVars (Universe _) = []
freeLVars (Act _ t) = freeLVars t
freeLVars (Comp _ e1 e2) = freeLVars e1 `union` freeLVars e2
freeLVars (Inv _ e) = freeLVars e
freeLVars (Fibr _ _ e1 e2) = freeLVars e1 `union` freeLVars e2

freeLVarsDep :: [([String],Term)] -> Term -> [DBIndex]
freeLVarsDep [] e = freeLVars e
freeLVarsDep ((vars,t):vs) e = freeLVars t `union` map (\l -> l - genericLength vars) (freeLVarsDep vs e)

liftTermDB :: DBIndex -> Term -> Term
liftTermDB = liftTermDB' 0

liftTermDB' :: DBIndex -> DBIndex -> Term -> Term
liftTermDB' n k (Let defs e) = Let (map (liftTermDBDef n k) defs) e
liftTermDB' n k (Lam m vars e) = Lam m vars $ liftTermDB' (genericLength vars + n) k e
liftTermDB' n k (Pi m vars e) =
    let (v,l) = liftTermDBVars n k vars
    in Pi m v (liftTermDB' l k e)
liftTermDB' n k (Sigma m  vars e) =
    let (v,l) = liftTermDBVars n k vars
    in Sigma m v (liftTermDB' l k e)
liftTermDB' n k (Id m t e1 e2) = Id m (liftTermDB' n k t) (liftTermDB' n k e1) (liftTermDB' n k e2)
liftTermDB' n k (App m e1 e2) = App m (liftTermDB' n k e1) (liftTermDB' n k e2)
liftTermDB' n k (Pair e1 e2) = Pair (liftTermDB' n k e1) (liftTermDB' n k e2)
liftTermDB' _ _ NoVar = NoVar
liftTermDB' _ _ e@(Var _) = e
liftTermDB' n k (LVar i) | i < n = LVar i
                         | otherwise = LVar (i + k)
liftTermDB' _ _ Nat = Nat
liftTermDB' _ _ Suc = Suc
liftTermDB' _ _ Rec = Rec
liftTermDB' _ _ Idp = Idp
liftTermDB' n k (Pmap e1 e2) = Pmap (liftTermDB' n k e1) (liftTermDB' n k e2)
liftTermDB' n k (Act t e) = Act t (liftTermDB' n k e)
liftTermDB' n k (Comp m e1 e2) = Comp m (liftTermDB' n k e1) (liftTermDB' n k e2)
liftTermDB' n k (Inv m e) = Inv m (liftTermDB' n k e)
liftTermDB' n k (Fibr d m e1 e2) = Fibr d m (liftTermDB' n k e1) (liftTermDB' n k e2)
liftTermDB' _ _ Coe = Coe
liftTermDB' _ _ Proj1 = Proj1
liftTermDB' _ _ Proj2 = Proj2
liftTermDB' _ _ Iso = Iso
liftTermDB' _ _ Pcon = Pcon
liftTermDB' _ _ e@(NatConst _) = e
liftTermDB' _ _ e@(Universe _) = e

liftTermDBVars :: DBIndex -> DBIndex -> [([String],Term)] -> ([([String],Term)],DBIndex)
liftTermDBVars n _ [] = ([], n)
liftTermDBVars n k ((vars,t):vs) =
    let (r, n') = liftTermDBVars (n + genericLength vars) k vs
    in ((vars, liftTermDB' n k t) : r, n')

liftTermDBDef :: DBIndex -> DBIndex -> Def -> Def
liftTermDBDef n k (Def name Nothing expr) = Def name Nothing (liftTermDB' n k expr)
liftTermDBDef n k (Def name (Just (ty, args)) expr) =
    Def name (Just (liftTermDB' n k ty, args)) $ liftTermDB' (n + genericLength args) k expr

instance Eq Term where
    (==) = cmp 0 M.empty M.empty
      where
        cmp :: Int -> M.Map String Int -> M.Map String Int -> Term -> Term -> Bool
        cmp c m1 m2 (Act a e1) e2 | isIdc a = cmp c m1 m2 e1 e2
        cmp c m1 m2 e1 (Act a e2) | isIdc a = cmp c m1 m2 e1 e2
        cmp c m1 m2 (Let [] e1) e2 = cmp c m1 m2 e1 e2
        cmp c m1 m2 e1 (Let [] e2) = cmp c m1 m2 e1 e2
        cmp c m1 m2 (Let (Def v1 Nothing r1 : ds1) e1) (Let (Def v2 Nothing r2 : ds2) e2) =
            cmp c m1 m2 r1 r2 && cmp (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) (Let ds1 e1) (Let ds2 e2)
        cmp c m1 m2 (Let (Def v1 (Just (t1,_)) r1 : ds1) e1) (Let (Def v2 (Just (t2,_)) r2 : ds2) e2) =
            cmp c m1 m2 t1 t2 && cmp c m1 m2 r1 r2 &&
            cmp (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) (Let ds1 e1) (Let ds2 e2)
        cmp c m1 m2 (Lam n1 [] e1) (Lam n2 [] e2) = n1 == n2 && cmp c m1 m2 e1 e2
        cmp c m1 m2 (Lam n1 (_:vs1) e1) (Lam n2 (_:vs2) e2) = cmp c m1 m2 (Lam n1 vs1 e1) (Lam n2 vs2 e2)
        cmp c m1 m2 (Pi n1 ts1 e1) (Pi n2 ts2 e2) = n1 == n2 && cmp'dep c m1 m2 n1 ts1 e1 n2 ts2 e2
        cmp c m1 m2 (Sigma n1 ts1 e1) (Sigma n2 ts2 e2) = n1 == n2 && cmp'dep c m1 m2 n1 ts1 e1 n2 ts2 e2
        cmp c m1 m2 (Id n1 t1 a1 b1) (Id n2 t2 a2 b2) =
            n1 == n2 && cmp c m1 m2 t1 t2 && cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (App n1 a1 b1) (App n2 a2 b2) = n1 == n2 && cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Pair a1 b1) (Pair a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Pmap a1 b1) (Pmap a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Act t1 e1) (Act t2 e2) = t1 == t2 && cmp c m1 m2 e1 e2
        cmp c m1 m2 (Comp k1 a1 b1) (Comp k2 a2 b2) = k1 == k2 && cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Inv k1 e1) (Inv k2 e2) = k1 == k2 && cmp c m1 m2 e1 e2
        cmp c m1 m2 (Fibr d1 n1 a1 b1) (Fibr d2 n2 a2 b2) = d1 == d2 && n1 == n2 && cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (LVar v1) (LVar v2) = v1 == v2
        cmp _ m1 m2 (Var v1) (Var v2) = M.lookup v1 m1 == M.lookup v2 m2
        cmp _ _ _ NoVar NoVar = True
        cmp _ _ _ Nat Nat = True
        cmp _ _ _ Suc Suc = True
        cmp _ _ _ Rec Rec = True
        cmp _ _ _ Idp Idp = True
        cmp _ _ _ Coe Coe = True
        cmp _ _ _ Proj1 Proj1 = True
        cmp _ _ _ Proj2 Proj2 = True
        cmp _ _ _ Iso Iso = True
        cmp _ _ _ Pcon Pcon = True
        cmp _ _ _ (NatConst c1) (NatConst c2) = c1 == c2
        cmp _ _ _ (Universe l1) (Universe l2) = l1 == l2
        cmp _ _ _ _ _ = False
        
        cmp'dep c m1 m2 _ [] e1 _ [] e2 = cmp c m1 m2 e1 e2
        cmp'dep c m1 m2 _ [] e1 n2 ts2 e2 = cmp c m1 m2 e1 (Pi n2 ts2 e2)
        cmp'dep c m1 m2 n1 ts1 e1 _ [] e2 = cmp c m1 m2 (Pi n1 ts1 e1) e2
        cmp'dep c m1 m2 n1 ((vs1,t1):ts1) e1 n2 ((vs2,t2):ts2) e2 = cmp c m1 m2 t1 t2 && case drop vs1 vs2 of
            ([],[]) -> cmp'dep c m1 m2 n1 ts1 e1 n2 ts2 e2
            ([],vs2') -> cmp'dep c m1 m2 n1 ts1 e1 n2 ((vs2',t2):ts2) e2
            (vs1',_) -> cmp'dep c m1 m2 n1 ((vs1',t1):ts1) e1 n2 ts2 e2
          where
            drop (_:vs1) (_vs2) = drop vs1 vs2
            drop vs1 vs2 = (vs1,vs2)

ppDef :: [String] -> Def -> Doc
ppDef ctx (Def name Nothing          expr) = text name <+> equals <+> ppTerm ctx Nothing expr
ppDef ctx (Def name (Just (ty,args)) expr) =
    let (args',ctx') = addVars args ctx
    in  text name <+> colon  <+> ppTerm ctx Nothing ty
    $+$ text name <+> hsep (map text args') <+> equals <+> ppTerm ctx' Nothing expr

safeIndex :: [a] -> DBIndex -> Maybe a
safeIndex [] _ = Nothing
safeIndex (x:_) 0 = Just x
safeIndex (_:xs) n = safeIndex xs (n - 1)

ppTerm :: [String] -> Maybe Int -> Term -> Doc
ppTerm ctx = go ctx False
  where
    ppArrow ctx l e@(Lam _ _ _) = go ctx True l e
    ppArrow ctx l e@(Pi _ _ _) = go ctx True l e
    ppArrow ctx l e = go ctx False l e
    
    isComp (Let _ _) = True
    isComp (Lam _ _ _) = True
    isComp (Pi _ _ _) = True
    isComp (Sigma _ _ _) = True
    isComp (Id _ _ _ _) = True
    isComp _ = False
    
    ppId ctx l e@(Lam _ _ _) = go ctx True l e
    ppId ctx l e@(Pi _ _ _) = go ctx True l e
    ppId ctx l e@(Id _ _ _ _) = go ctx True l e
    ppId ctx l e = go ctx False l e
    
    ppVars :: [String] -> Bool -> Char -> Maybe Int -> [([String],Term)] -> ([String],Doc)
    ppVars ctx _ c l [] = (ctx, char c)
    ppVars ctx True c l ts = second (char c <+>) (ppVars ctx False c l ts)
    ppVars ctx False c l (([],t):ts) =
        let l' = fmap pred l
        in second (ppArrow ctx l' t <+>) (ppVars ctx True c l' ts)
    ppVars ctx False c l ((vars,t):ts) =
        let l' = fmap pred l
            b = not (null ts) && null (fst $ head ts)
            (vars',ctx') = addVars vars ctx
        in second (parens (hsep (map text vars') <+> colon <+> go ctx False l' t) <+>)
                  (ppVars ctx' b c l' ts)
    
    dim 0 = empty
    dim n = char '<' <> integer n <> char '>'
    
    go :: [String] -> Bool -> Maybe Int -> Term -> Doc
    go _ _ (Just 0) _ = char '_'
    go _ _ _ (NatConst n) = integer n
    go _ _ _ x | Just n <- getNat x = integer n
      where
        getNat :: Term -> Maybe Integer
        getNat (NatConst n) = Just n
        getNat (App 0 Suc x) = fmap succ (getNat x)
        getNat _ = Nothing
    go _ _ _ NoVar = text "_"
    go _ _ _ (Var v) = text v
    go ctx _ _ (LVar v) = text $ maybe ("<" ++ show v ++ ">") id (ctx `safeIndex` v)
    go _ _ _ Nat = text "Nat"
    go _ _ _ Suc = text "suc"
    go _ _ _ Rec = text "R"
    go _ _ _ Idp = text "idp"
    go _ _ _ Coe = text "coe"
    go _ _ _ Proj1 = text "proj1"
    go _ _ _ Proj2 = text "proj2"
    go _ _ _ Iso = text "iso"
    go _ _ _ Pcon = text "pcon"
    go _ _ _ (Universe u) = text (show u)
    go ctx True l e = parens (go ctx False l e)
    go ctx False l (Let defs e) = text "let" <+> vcat (map (ppDef ctx) defs) $+$ text "in" <+> go ctx False l e
    go ctx False l (Lam n vars e) =
        let (vars',ctx') = addVars vars ctx
        in char 'λ' <> dim n <> hsep (map text vars') <+> char '→' <+> go ctx' False (fmap pred l) e
    go ctx False l (Pi n ts e) =
        let l' = fmap pred l
            (ctx',r) = ppVars ctx False '→' l' ts
        in (if n == 0 then empty else text "Pi" <> dim n) <> r <+> go ctx' False l' e
    go ctx False l (Sigma n ts e) =
        let l' = fmap pred l
            (ctx',r) = ppVars ctx False '×' l' ts
        in (if n == 0 then empty else text "Sigma" <> dim n) <> r <+> ppArrow ctx' l' e
    go ctx False l (Id 0 t e1 e2) =
        let l' = fmap pred l
        in ppId ctx l' e1 <+> equals <+> ppId ctx l' e2 <+> char '|' <+> go ctx False l' t
    go ctx False l (Id n t e1 e2) =
        let l' = fmap pred l
        in text "Id" <> dim n <+> go ctx True l' t <+> go ctx True l' e1 <+> go ctx True l' e2
    go ctx False l (App n e1 e2) =
        let l' = fmap pred l
        in go ctx False l' e1 <+> dim n <+> go ctx True l' e2
    go ctx False l (Pair e1 e2) =
        let l' = fmap pred l
        in go ctx False l' e1 <> comma <+> go ctx False l' e2
    go ctx False l (Comp n e1 e2) =
        let l' = fmap pred l
        in text "comp" <> dim n <+> go ctx True l' e1 <+> go ctx True l' e2
    go ctx False l (Inv n e) = text "inv" <> dim n <+> go ctx True (fmap pred l) e
    go ctx False l (Fibr d n e1 e2) =
        let l' = fmap pred l
        in text (if d then "opfibr" else "fibr") <> dim n <+> go ctx True l' e1 <+> go ctx True l' e2
    go ctx False l (Pmap e1 e2) =
        let l' = fmap pred l
        in go ctx False l' e1 <+> text "<*>" <+> go ctx True l' e2
    go ctx False l (Act t e) = text ('@' : show t) <+> go ctx True (fmap pred l) e

addVars :: [String] -> [String] -> ([String],[String])
addVars [] ctx = ([],ctx)
addVars (v:vs) ctx | v /= "_" && elem v ctx = addVars ((v ++ "'") : vs) ctx
                   | otherwise = first (v :) $ addVars vs (v : ctx)

simplify :: Term -> Term
simplify (Let [] e) = simplify e
simplify (Let defs (Let defs' e)) = simplify $ Let (defs ++ defs') e
simplify (Let defs e) = Let (map simplifyDef defs) (simplify e)
simplify (Lam _ [] e) = simplify e
simplify (Lam n args (Lam n' args' e)) | n == n' = simplify $ Lam n (args ++ args') e
simplify (Lam n args e) = Lam n (simplifyArgs (genericLength args - 1) args $ freeLVars e) (simplify e)
  where
    simplifyArgs _ [] _ = []
    simplifyArgs n (a:as) l | elem n l = (if a == "_" then "x" else a) : simplifyArgs (n - 1) as l
                            | otherwise = "_" : simplifyArgs (n - 1) as l
simplify (Pi _ [] e) = simplify e
simplify (Pi n (([],t):ts) e) = Pi n [([], simplify t)] $ simplify (Pi n ts e)
simplify (Pi n (([v],t):ts) e)
    | elem 0 (freeLVars $ Pi n ts e) = case simplify (Pi n ts e) of
        Pi n' ts' e' -> Pi n' (([v], simplify t):ts') e'
        r -> Pi n [([v], simplify t)] r
    | otherwise = case simplify (Pi n ts e) of
        Pi n' ts' e' ->
            let (ts'',e'') = lowerTermDB 0 ts' e'
            in Pi n' (([], simplify t) : ts'') e''
        r -> Pi n [([], simplify t)] (liftTermDB (-1) r)
simplify (Pi n ((v:vs,t):ts) e)
    | elem 0 (freeLVars $ Pi n ((vs,t):ts) e) = case simplify $ Pi n ((vs,t):ts) e of
        Pi n' ts' e' -> Pi n' (([v], simplify t):ts') e'
        r -> Pi n [([v], simplify t)] r
    | otherwise = Pi n [([], simplify t)] $ simplify $
        let (ts',e') = lowerTermDB (genericLength vs) ts e
        in Pi n ((vs,t) : ts') e'
simplify (Sigma _ [] e) = simplify e
simplify (Sigma n (([],t):ts) e) = Sigma n [([], simplify t)] $ simplify (Sigma n ts e)
simplify (Sigma n (([v],t):ts) e)
    | elem 0 (freeLVars $ Sigma n ts e) = case simplify (Sigma n ts e) of
        Sigma n' ts' e' -> Sigma n' (([v], simplify t):ts') e'
        r -> Sigma n [([v], simplify t)] r
    | otherwise = case simplify (Sigma n ts e) of
        Sigma n' ts' e' ->
            let (ts'',e'') = lowerTermDB 0 ts' e'
            in Sigma n' (([], simplify t) : ts'') e''
        r -> Sigma n [([], simplify t)] (liftTermDB (-1) r)
simplify (Sigma n ((v:vs,t):ts) e)
    | elem 0 (freeLVars $ Sigma n ((vs,t):ts) e) = case simplify $ Sigma n ((vs,t):ts) e of
        Sigma n' ts' e' -> Sigma n' (([v], simplify t):ts') e'
        r -> Sigma n [([v], simplify t)] r
    | otherwise = Sigma n [([], simplify t)] $ simplify $
        let (ts',e') = lowerTermDB (genericLength vs) ts e
        in Sigma n ((vs,t) : ts') e'
simplify (Id n t a b) = Id n (simplify t) (simplify a) (simplify b)
simplify (App n e1 e2) = App n (simplify e1) (simplify e2)
simplify (Pair e1 e2) = Pair (simplify e1) (simplify e2)
simplify (Pmap e1 e2) = Pmap (simplify e1) (simplify e2)
simplify (Act t e) | isIdc t = simplify e
simplify (Act t1 (Act t2 e)) = simplify $ Act (composec t1 t2) e
simplify (Act t e) = Act t (simplify e)
simplify (Comp k e1 e2) = Comp k (simplify e1) (simplify e2)
simplify (Inv k e) = Inv k (simplify e)
simplify (Fibr d n e1 e2) = Fibr d n (simplify e1) (simplify e2)
simplify e@(Var _) = e
simplify e@(LVar _) = e
simplify NoVar = NoVar
simplify Nat = Nat
simplify Suc = Suc
simplify Rec = Rec
simplify Idp = Idp
simplify Coe = Coe
simplify Proj1 = Proj1
simplify Proj2 = Proj2
simplify Iso = Iso
simplify Pcon = Pcon
simplify e@(NatConst _) = e
simplify e@(Universe _) = e

lowerTermDB :: DBIndex -> [([String],Term)] -> Term -> ([([String],Term)],Term)
lowerTermDB k [] e = ([], liftTermDB' k (-1) e)
lowerTermDB k ((vars,t):ts) e =
    let (ts',e') = lowerTermDB (k + genericLength vars) ts e
    in ((vars, liftTermDB' k (-1) t) : ts', e')

simplifyDef :: Def -> Def
simplifyDef (Def name Nothing expr) = Def name Nothing (simplify expr)
simplifyDef (Def name (Just (ty,args)) expr) =
    let (args',expr') = extractArgs (simplify expr)
    in Def name (Just (simplify ty, args ++ args')) expr'
  where
    extractArgs :: Term -> ([String],Term)
    extractArgs (Lam _ xs e) = let (ys,r) = extractArgs e in (xs ++ ys, r)
    extractArgs e = ([],e)
