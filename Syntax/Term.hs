module Syntax.Term
    ( Term(..), Def(..), Level(..)
    , ppTerm, ppDef
    , freshName, freeVars
    ) where

import qualified Data.Map as M
import Text.PrettyPrint
import Data.List

data Level = Finite Integer | Omega | Omega1 | Omega2 deriving Eq

instance Show Level where
    show (Finite n) = "Type" ++ show n
    show Omega = "Type"
    show Omega1 = "TYPE"
    show Omega2 = "TYPE1"

instance Ord Level where
    compare (Finite x) (Finite y) = compare x y
    compare (Finite _) _ = LT
    compare _ (Finite _) = GT
    compare Omega Omega = EQ
    compare Omega Omega1 = LT
    compare Omega Omega2 = LT
    compare Omega1 Omega1 = EQ
    compare Omega1 Omega2 = LT
    compare Omega2 Omega2 = EQ
    compare _ _ = GT

instance Bounded Level where
    minBound = Finite 0
    maxBound = Omega2

instance Enum Level where
    succ (Finite l) = Finite (succ l)
    succ Omega = Omega1
    succ Omega1 = Omega2
    succ Omega2 = error "Enum.Level.succ: bad argument"
    pred (Finite l) | l > 0 = Finite (pred l)
    pred Omega1 = Omega
    pred Omega2 = Omega1
    pred _ = error "Enum.Level.pred: bad argument"
    toEnum = Finite . toInteger
    fromEnum (Finite l) = fromInteger l
    fromEnum _ = error "Enum.Level.fromEnum: bad argument"

data Def = Def String (Maybe (Term,[String])) Term

data Term
    = Let [Def] Term
    | Lam [String] Term
    | Pi [([String],Term)] Term
    | Sigma [([String],Term)] Term
    | Id Term Term
    | App Term Term
    | Var String
    | Nat
    | Suc
    | Rec
    | Idp
    | Pmap Term
    | NatConst Integer
    | Universe Level

freshName :: String -> [String] -> String
freshName "_" vars = freshName "x" vars
freshName base vars | elem base vars = go 0
                    | otherwise = base
  where
    go n | elem x vars = go (n + 1)
         | otherwise = x
         where x = base ++ show n

freeVars :: Term -> [String]
freeVars (Let defs e) = freeVars e \\ map (\(Def name _ _) -> name) defs
freeVars (Lam [] e) = freeVars e
freeVars (Lam (v:vs) e) = delete v $ freeVars (Lam vs e)
freeVars (Pi [] e) = freeVars e
freeVars (Pi ((vars,t):vs) e) = freeVars t `union` (freeVars (Pi vs e) \\ vars)
freeVars (Sigma [] e) = freeVars e
freeVars (Sigma ((vars,t):vs) e) = freeVars t `union` (freeVars (Sigma vs e) \\ vars)
freeVars (Id e1 e2) = freeVars e1 `union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Var "_") = []
freeVars (Var v) = [v]
freeVars Nat = []
freeVars Suc = []
freeVars Rec = []
freeVars Idp = []
freeVars (Pmap e) = freeVars e
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
        cmp c m1 m2 (Id a1 b1) (Id a2 b2) = cmp c m1 m2 a1 a2 && cmp c m1 m2 b1 b2
        cmp c m1 m2 (Var v1) (Var v2) = case (M.lookup v1 m1, M.lookup v2 m2) of
            (Nothing, Nothing) -> v1 == v2
            (Just c1, Just c2) -> c1 == c2
            _ -> False
        cmp c m1 m2 (Pmap e1) (Pmap e2) = cmp c m1 m2 e1 e2
        cmp _ _ _ Nat Nat = True
        cmp _ _ _ Suc Suc = True
        cmp _ _ _ Rec Rec = True
        cmp _ _ _ Idp Idp = True
        cmp _ _ _ (NatConst c1) (NatConst c2) = c1 == c2
        cmp _ _ _ (Universe l1) (Universe l2) = l1 == l2
        cmp _ _ _ _ _ = False
        
        cmpVars c m1 m2 [] [] e1 e2 = cmp c m1 m2 e1 e2
        cmpVars c m1 m2 (v1:vs1) (v2:vs2) e1 e2 = cmpVars (c + 1) (M.insert v1 c m1) (M.insert v2 c m2) vs1 vs2 e1 e2
        cmpVars _ _ _ _ _ _ _ = False

ppDef :: Def -> Doc
ppDef (Def name Nothing          expr) = text name <+> equals <+> ppTerm Nothing expr
ppDef (Def name (Just (ty,args)) expr) = text name <+> colon  <+> ppTerm Nothing ty
                                     $+$ text name <+> equals <+> hsep (map text args) <+> ppTerm Nothing expr

ppTerm :: Maybe Int -> Term -> Doc
ppTerm = go False
  where
    ppArrow l e@(Lam _ _) = go True l e
    ppArrow l e@(Pi _ _) = go True l e
    ppArrow l e = go False l e
    
    ppVars :: Bool -> Char -> Maybe Int -> [([String],Term)] -> Term -> Doc
    ppVars _ c l [] e = char c <+> go False l e
    ppVars True c l ts e = char c <+> ppVars False c l ts e
    ppVars False c l (([],t):ts) e =
        let l' = fmap pred l
        in ppArrow l' t <+> ppVars True c l' ts e
    ppVars False c l ((vars,t):ts) e =
        let l' = fmap pred l
        in parens (hsep (map text vars) <+> colon <+> go False l' t) <+> ppVars False c l' ts e
    
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
    go _ _ (Universe u) = text (show u)
    go True l e = parens (go False l e)
    go False l (Let defs e) = text "let" <+> vcat (map ppDef defs) $+$ text "in" <+> go False l e
    go False l (Lam vars e) = char 'λ' <> hsep (map text vars) <+> char '→' <+> go False (fmap pred l) e
    go False l (Pi ts e) =
        let l' = fmap pred l
        in ppVars False '→' l' ts e
    go False l (Sigma ts e) =
        let l' = fmap pred l
        in ppVars False '×' l' ts e
    go False l (Id e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> equals <+> go False l' e2
    go False l (App e1 e2) =
        let l' = fmap pred l
        in go False l' e1 <+> go True l' e2
    go False l (Pmap e) = text "pmap" <+> go True (fmap pred l) e
