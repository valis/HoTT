module Eval
    ( eval
    , evalOfType
    ) where

import qualified Data.Map as M

import Parser.AbsGrammar
import Parser.PrintGrammar

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Level = Finite Integer | Omega | Omega1 | Omega2 deriving Eq
type ErrorMsg = String
data Value
    = Slam String (Integer -> GlobMap -> Value -> Value) -- Constructor for Pi-types
    | Szero | Ssuc Value -- Constructors for Nat
    | Spi Value String Value | Ssigma Value String Value | Snat | Sid Value Value | Stype Level -- Constructors for Type_k
    | Svar String | Sapp Value Value | Srec Value Value Value | Serror [ErrorMsg]
    -- | Srepl Value | Siso Value Value Value Value | Scomp Value Value | Ssym Value
type Ctx = M.Map String (Value,Value,Level)

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
    pred (Finite l) | l > 0= Finite (pred l)
    pred Omega1 = Omega
    pred Omega2 = Omega1
    pred _ = error "Enum.Level.pred: bad argument"
    toEnum = Finite . toInteger
    fromEnum (Finite l) = fromInteger l
    fromEnum _ = error "Enum.Level.fromEnum: bad argument"

checkValue2 :: (Value -> Value -> Value) -> Value -> Value -> Value
checkValue2 f (Serror m1) (Serror m2) = Serror (m1 ++ m2)
checkValue2 f (Serror m) _ = Serror m
checkValue2 f _ (Serror m) = Serror m
checkValue2 f v1 v2 = f v1 v2

maxType :: Bool -> Value -> Value -> Value
maxType _ (Stype k1) (Stype k2) = Stype (max k1 k2)
maxType True _ _ = Stype (Finite 0)
maxType False _ _ = Serror ["Expected type"]

checkError :: Value -> Value -> Level -> Level -> (Value,Value,Level)
checkError e1@(Serror _) e2@(Serror _) l1 l2 = (e1,e2,max l1 l2)
checkError e@(Serror _) _ l1 l2 = (e,e,max l1 l2)
checkError _ e@(Serror _) l1 l2 = (e,e,max l1 l2)
checkError v1 v2 l1 l2 = (v1,v2,max l1 l2)

retError :: [ErrorMsg] -> (Value,Value,Level)
retError errs = (Serror errs, Serror errs, maxBound)

action :: GlobMap -> Value -> Value
action _ v = v -- TODO: Define it

parseLevel :: String -> Level
parseLevel "Type" = Omega
parseLevel ('T':'y':'p':'e':s) = Finite (read s)

eval :: Expr -> Integer -> Ctx -> (Value,Value,Level)
eval (Lam _ _) _ _ = retError ["Cannot infer type of lambda expression"]
eval (Arr e1 e2) 0 ctx = let
    (v1, k1, l1) = eval e1 0 ctx
    (v2, k2, l2) = eval e2 0 ctx
    in checkError (Spi v1 "_" v2) (checkValue2 (maxType False) k1 k2) l1 l2
eval (Pi [] e) n ctx = eval e n ctx
eval (Pi (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Arr t (Pi vars e)) n ctx
eval (Pi (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx
  | M.member x ctx = undefined -- TODO: Define it
  | otherwise = case eval t 0 ctx of
        (v1, Stype k1, l1) -> let (v2, k2, l2) = eval (Pi vars e) 0 (M.insert x (Svar x,v1,k1) ctx)
                              in checkError (Spi v1 x v2) (checkValue2 (maxType False) (Stype k1) k2) l1 l2
        _ -> retError ["Expected type"]
eval (Pi (TypedVar _ t : vars) e) 0 ctx = retError ["Expected identifier"]
eval (Prod e1 e2) 0 ctx = let
    (v1, k1, l1) = eval e1 0 ctx
    (v2, k2, l2) = eval e2 0 ctx
    in checkError (Ssigma v1 "_" v2) (checkValue2 (maxType False) k1 k2) l1 l2
eval (Sigma [] e) n ctx = eval e n ctx
eval (Sigma (TypedVar (Var NoArg) t : vars) e) n ctx = eval (Prod t (Sigma vars e)) n ctx
eval (Sigma (TypedVar (Var (Arg (PIdent (_,x)))) t : vars) e) 0 ctx
  | M.member x ctx = undefined -- TODO: Define it
  | otherwise = case eval t 0 ctx of
        (v1, Stype k1, l1) -> let (v2, k2, l2) = eval (Pi vars e) 0 (M.insert x (Svar x,v1,k1) ctx)
                              in checkError (Ssigma v1 x v2) (checkValue2 (maxType False) (Stype k1) k2) l1 l2
        _ -> retError ["Expected type"]
eval (Sigma (TypedVar _ t : vars) e) 0 ctx = retError ["Expected identifier"]
eval (Id a b) 0 ctx = let
    (va,ta,la) = eval a 0 ctx
    (vb,tb,lb) = evalOfType b ta la 0 ctx
    in (Sid va vb, maxType True tb ta, max la lb)
eval Nat 0 _ = (Snat, Stype (Finite 0), Finite 1)
eval (Universe (U t)) 0 _ = let lvl = parseLevel t in (Stype lvl, Stype (succ lvl), succ $ succ lvl)
eval (App e1 e2) n ctx = undefined
eval (Var x) n ctx = undefined
eval Suc n ctx = undefined
eval (NatConst x) n ctx = undefined
eval Rec n ctx = undefined

evalOfType :: Expr -> Value -> Level -> Integer -> Ctx -> (Value,Value,Level)
evalOfType (Lam [] e) ty lvl n ctx = evalOfType e ty lvl n ctx
evalOfType (Lam (Binder NoArg:xs) e) (Spi a _ b) lvl n ctx = (Slam "_" $ \k m _ -> let
    (r,_,_) = evalOfType (Lam xs e) b lvl k $ M.map (\(v,t,l) -> (action m v,t,l)) ctx in r, Spi a "_" b, lvl)
evalOfType (Lam (Binder (Arg (PIdent (_,x))):xs) e) (Spi a y b) lvl n ctx
  | M.member x ctx = undefined -- TODO: Define it
  | otherwise = (Slam x $ \k m v -> let
        m' = M.insert x (v,a,lvl) $ M.map (\(v,t,l) -> (action m v,t,l)) ctx
        (r,_,_) = evalOfType (Lam xs e) (renameValue b y x) lvl k m'
        in r, Spi a y b, lvl)
evalOfType (Lam _ _) ty _ _ _ = case reify ty (Stype maxBound) of
    Left errs -> retError errs
    Right e -> retError ["Expected pi type\nActual type: " ++ show e]
evalOfType e ty lvl n ctx = let
    (r,ty1,lvl1) = eval e n ctx
    te = reify ty (Stype lvl)
    te1 = reify ty1 (Stype lvl1)
    in case (te,te1) of
        (Left errs,_) -> retError errs
        (_,Left errs) -> retError errs
        (Right te', Right te1') -> if te1' <= te' then (r,ty1,lvl1) else
            retError ["Expected type: " ++ show te' ++ "\nActual type: " ++ show te1']

newtype Norm = Norm Expr

instance Eq Norm where
    Norm e1 == Norm e2 = e1 == e2 -- TODO: alpha conversion?

instance Ord Norm where
    Norm e1 <= Norm e2 = e1 == e2 -- TODO: Define it

instance Show Norm where
    show (Norm e) = printTree e

reify :: Value -> Value -> Either [ErrorMsg] Norm
reify = undefined

rename :: Expr -> String -> String -> Expr
rename e x y | x == y = e
rename _ _ _ = undefined

renameValue :: Value -> String -> String -> Value
renameValue v x y | x == y = v
renameValue _ _ _ = undefined
