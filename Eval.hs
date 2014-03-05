module Eval
    ( eval
    , evalOfType
    ) where

import qualified Data.Map as M

import Parser.AbsGrammar
import Parser.PrintGrammar

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Level = Finite Integer | Omega | Omega1 deriving Eq
type ErrorMsg = String
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi Value String Value | Ssigma Value String Value | Snat | Sid Value Value | Stype Level -- Constructors for Type_k
    | Svar String | Sapp Value Value | Srec Value Value Value | Serror [ErrorMsg]
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx = M.Map String (Value,Value)

instance Ord Level where
    compare (Finite x) (Finite y) = compare x y
    compare (Finite _) _ = LT
    compare _ (Finite _) = GT
    compare Omega Omega1 = LT
    compare Omega1 Omega = GT
    compare _ _ = EQ

instance Bounded Level where
    minBound = Finite 0
    maxBound = Omega1

checkValue2 :: (Value -> Value -> Value) -> Value -> Value -> Value
checkValue2 f (Serror m1) (Serror m2) = Serror (m1 ++ m2)
checkValue2 f (Serror m) _ = Serror m
checkValue2 f _ (Serror m) = Serror m
checkValue2 f v1 v2 = f v1 v2

maxType :: Value -> Value -> Value
maxType (Stype k1) (Stype k2) = Stype (max k1 k2)
maxType _ _ = Serror ["Expected type"]

checkError :: Value -> Value -> (Value,Value)
checkError e1@(Serror _) e2@(Serror _) = (e1,e2)
checkError e@(Serror _) _ = (e,e)
checkError _ e@(Serror _) = (e,e)
checkError v1 v2 = (v1,v2)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Определи-ка.

eval :: Expr -> Integer -> Ctx -> (Value,Value)
eval (Lam _ _) _ _ = let err = Serror ["Cannot infer type of lambda expression"] in (err,err)
eval (Arr e1 e2) 0 ctx = let
    (v1, k1) = eval e1 0 ctx
    (v2, k2) = eval e2 0 ctx
    in checkError (Spi v1 "_" v2) (checkValue2 maxType k1 k2)
eval (Pi [] e) n ctx = eval e n ctx
eval (Pi (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Arr t (Pi vars e)) n ctx
eval (Pi (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx
  | M.member x ctx = undefined -- TODO: Определи-ка.
  | otherwise = let
    (v1, k1) = eval t 0 ctx
    (v2, k2) = eval (Pi vars e) 0 (M.insert x (Svar x,v1) ctx)
    in checkError (Spi v1 x v2) (checkValue2 maxType k1 k2)
eval (Pi (TypedVar _ t : vars) e) 0 ctx = let err = Serror ["Expected identifier"] in (err,err)
eval _ _ _ = undefined

-- (\f -> refl (f 0) :: (f : Nat -> Nat) -> f 0 = f 0) (\x -> x + 1)

evalOfType :: Expr -> Value -> Integer -> Ctx -> Value
evalOfType (Lam [] e) ty n ctx = evalOfType e ty n ctx
evalOfType (Lam (Binder NoArg:xs) e) (Spi a _ b) n ctx =
    Slam "_" $ \k m _ -> evalOfType (Lam xs e) b k $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType (Lam (Binder (Arg (PIdent (_,x))):xs) e) (Spi a y b) n ctx
  | M.member x ctx = undefined -- TODO: Определи-ка.
  | otherwise = Slam x $ \k m v -> evalOfType (Lam xs e) (renameValue b y x) k
    $ M.insert x (v,a) $ M.map (\(v,t) -> (action m v,t)) ctx
evalOfType (Lam _ _) ty _ _ = case reify ty (Stype maxBound) of
    Left errs -> Serror errs
    Right e -> Serror ["Expected pi type\nActual type: " ++ printTree e]
evalOfType e ty n ctx = let
    (r,ty1) = eval e n ctx
    te = reify ty (Stype maxBound)
    te1 = reify ty1 (Stype maxBound)
    in case (te,te1) of
        (Left errs,_) -> Serror errs
        (_,Left errs) -> Serror errs
        (Right te', Right te1') -> if te' == te1' then r else
            Serror ["Expected type: " ++ printTree te' ++ "\nActual type: " ++ printTree te1']

reify :: Value -> Value -> Either [ErrorMsg] Expr
reify = undefined

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename _ _ _ = undefined

renameValue :: Value -> String -> String -> Value
renameValue v x y | x == y = v
renameValue _ _ _ = undefined

{-
newtype PIdent = PIdent ((Int,Int),String) deriving (Eq,Ord,Show)

data Expr =
   Lam [Binder] Expr
 | Arr Expr Expr
 | Pi [TypedVar] Expr
 | Prod Expr Expr
 | Sigma [TypedVar] Expr
 | Id Expr Expr
 | App Expr Expr
 | Var Arg
 | Nat
 | Suc
 | Rec
 | NatConst Integer
 | Universe U

data Arg =
   Arg PIdent
 | NoArg

data Binder =
   Binder Arg

data TypedVar =
   TypedVar Expr Expr
-}
