module Syntax.Raw
    ( unArg, unBinder
    , getPos, argGetPos, binderGetPos
    , parseLevel
    , freeVars, rename, renameExpr
    , processDefs
    ) where

import Data.List

import Parser.AbsGrammar
import Parser.PrintGrammar(printTree)
import qualified Syntax.Term as T
import ErrorDoc

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
getPos (Pmap (Ppmap (p,_)) _) = p
getPos (NatConst (PInt (p,_))) = p
getPos (Universe (U (p,_))) = p
getPos (Paren (PPar (p,_)) _) = p

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

parseLevel :: String -> T.Level
parseLevel "Type" = T.Omega
parseLevel ('T':'y':'p':'e':s) = T.Finite (read s)
parseLevel s = error $ "parseLevel: " ++ s

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
freeVars (Var (Arg (PIdent (_,x)))) = [x]
freeVars (Var (NoArg _)) = []
freeVars (Nat _) = []
freeVars (Suc _) = []
freeVars (Rec _) = []
freeVars (Idp _) = []
freeVars (Pmap _ e) = freeVars e
freeVars (NatConst _) = []
freeVars (Universe _) = []
freeVars (Paren _ e) = freeVars e

renameExpr :: [String] -> String -> Expr -> (String,Expr)
renameExpr m x e = let x' = T.freshName x (freeVars e ++ m) in (x', rename e x x')

renameDefs :: [Def] -> Expr -> String -> String -> ([Def],Expr)
renameDefs [] e x y = ([], rename e x y)
renameDefs r@(DefType (PIdent (i,z)) t : defs) e x y
    | z == x = (r,e)
    | z == y =
        let (y', Let defs1 e1) = renameExpr [z,x] y (Let defs e)
            (defs2, e2) = renameDefs defs1 e1 x y
        in (DefType (PIdent (i,y')) (rename t x y) : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
        in (DefType (PIdent (i,z)) (rename t x y) : defs', e')
renameDefs r@(Def (PIdent (i,z)) as t : defs) e x y
    | z == x = (r,e)
    | z == y =
        let (y', Let defs1 e1) = renameExpr [z,x] y (Let defs e)
            (defs2, e2) = renameDefs defs1 e1 x y
            Lam _ as' t' = rename (Lam (error "renameDefs.==") (map Binder as) t) x y
        in (Def (PIdent (i,y')) (map (\(Binder a) -> a) as') t' : defs2, e2)
    | otherwise =
        let (defs',e') = renameDefs defs e x y
            Lam _ as' t' = rename (Lam (error "renameDefs./=") (map Binder as) t) x y
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
rename (Var (Arg (PIdent (i,z)))) x y | x == z = Var $ Arg $ PIdent (i,y)
rename e@(Var _) _ _ = e
rename e@(Nat _) _ _ = e
rename e@(Suc _) _ _ = e
rename e@(Rec _) _ _ = e
rename e@(Idp _) _ _ = e
rename (Pmap i e) x y = Pmap i (rename e x y)
rename e@(NatConst _) _ _ = e
rename e@(Universe _) _ _ = e
rename (Paren i e) x y = Paren i (rename e x y)

processDefs :: [Def] -> EDocM [(String,Maybe Expr,[Arg],Expr)]
processDefs defs =
    let typeSigs = filterTypeSigs defs
        funDecls = filterFunDecls defs
        typeSigs' = map (\(PIdent (_,s),e) -> (s,e)) typeSigs
        funDecls' = map (\(PIdent (_,s),e) -> (s,e)) funDecls
        typeSigsDup = duplicates (map fst typeSigs)
        funDeclsDup = duplicates (map fst funDecls)
    in if not (null typeSigsDup) || not (null funDeclsDup)
        then Left $ map (\(PIdent ((l,c),s)) -> emsgLC l c ("Duplicate type signatures for " ++ s) enull) typeSigsDup
                 ++ map (\(PIdent ((l,c),s)) -> emsgLC l c ("Multiple declarations of " ++ s) enull) funDeclsDup
        else Right $ map (\(name,(args,expr)) -> (name,lookup name typeSigs',args,expr)) funDecls'
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

instance EPretty Expr where
    epretty = etext . printTree -- TODO: Reimplement printTree?
