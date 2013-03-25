module Normalization where

import qualified Data.Map as M
import Test.HUnit
import Data.List
import Data.Maybe

infixl 5 `App`
data Term = Var String | Lam String Term Term | App Term Term | Zero
    | Suc | R Term Term Term Term | Top | Bot | Unit | Pi Term
    | Id Term | Refl Term | Cong Term Term | Nat | Type Integer
newtype Norm = Norm Term deriving (Eq, Show)

arr :: Term -> Term -> Term
arr a b = Pi (Lam "_" a b)

instance Eq Term where
    (==) = eq 0
      where
        eq _ Zero Zero = True
        eq _ Suc Suc = True
        eq _ Top Top = True
        eq _ Bot Bot = True
        eq _ Unit Unit = True
        eq _ Nat Nat = True
        eq _ (Type k) (Type k') = k == k'
        eq _ (Var x) (Var x') = x == x'
        eq n (Refl t) (Refl t') = eq n t t'
        eq n (Cong t s) (Cong t' s') = eq n t t' && eq n s s'
        eq n (Id t) (Id t') = eq n t t'
        eq n (App t s) (App t' s') = eq n t t' && eq n s s'
        eq n (Lam x t s) (Lam x' t' s') = eq n t t' &&
            eq (n + 1) (rename s x (' ':show n)) (rename s' x' (' ':show n))
        eq n (Pi t) (Pi t') = eq n t t'
        eq n (R t z s p) (R t' z' s' p') = eq n t t' && eq n z z' && eq n s s' && eq n p p'
        eq _ _ _ = False

typeOf :: M.Map String Term -> Term -> Maybe Term
typeOf m (Var x) = M.lookup x m
typeOf m (Refl x) = Just (Id x `App` x)
{-
typeOf m (Lam x t f) = if M.member x m
    then typeOf (Lam (x ++ "'") t f) m
    else case typeOf (f x) (M.insert x t m) of
        Nothing -> Nothing
        Just s -> Just $ Pi x t (\y -> rename x y s)
  where
    rename :: String -> String -> Term -> Term
    rename = undefined
typeOf m (App x y) = case (typeOf m x, typeOf m y) of
    (Just (Pi v t f), Just r) | t == r -> App (Lam v t f) y
    _ -> Nothing
typeOf _ Zero = Just Nat
typeOf _ Suc = Just (arr Nat Nat)
typeOf _ (R t) = Just $ arr (App t Zero) $ arr (Pi "x" Nat $ \x -> arr (App t (Var x)) $ App t $ App Suc (Var x)) $ Pi "x" Nat (App t . Var)
typeOf _ Unit = Just Top
typeOf m (Repl _ _) = 
typeOf m (Cong _ _)
typeOf _ = Just Unit
-}

instance Show Term where
    show = show' False
      where
        addParens True s = "(" ++ s ++ ")"
        addParens False s = s
        
        showArrow e@(Lam _ _ _) = show' True e
        showArrow e@(Pi _) = show' True e
        showArrow e = show e
        
        show' _ x | Just n <- getNat x = show n
          where getNat Zero = Just 0
                getNat (App Suc x) = fmap succ (getNat x)
                getNat _ = Nothing
        show' _ (Var x) = x
        show' _ Suc = "S"
        show' _ Top = "Top"
        show' _ Bot = "Bot"
        show' _ Unit = "Unit"
        show' _ Nat = "Nat"
        show' _ (Type k) = "Type_" ++ show k
        show' par (Lam x t s) = addParens par $ "\\" ++ x ++ ":" ++ showArrow t ++ ". " ++ show s
        show' par (Id a) = "_=_ " ++ show' True a
        show' par (App (Id a) b) = addParens par $ show' True a ++ " = " ++ show' True b
        show' par (App a b) = addParens par $ show a ++ " " ++ show' True b
        show' par (R t z s n) = addParens par $
            "R " ++ show' True t ++ " " ++ show' True z ++ " " ++ show' True s ++ " " ++ show' True n
        show' par (Pi (Lam "_" t s)) = addParens par $ show' True t ++ " -> " ++ show s
        show' par (Pi (Lam x t s)) = addParens par $ "(" ++ x ++ " : " ++ show t ++ ") -> " ++ show s
        show' par (Pi _) = error "show: Pi without Lam"
        show' par (Refl x) = addParens par $ "refl " ++ show' True x
        show' par (Cong t s) = addParens par $ "cong " ++ show' True t ++ " " ++ show' True s

data D = Ld | Rd | Ud
type GlobMap = [D]
data Sem
    = Slam String Sem (Integer -> GlobMap -> Sem -> Sem) -- Constructor for Pi-types
    | Szero | Ssuc Sem -- Constructors for Nat
    | Sunit -- Constructor for Top
    | Spi Sem | Snat | Stop | Sbot | Sid Sem Sem | Stype Integer -- Constructors for Type_k
type Ctx = M.Map String Sem

action :: GlobMap -> Sem -> Sem
action a (Slam x t f) = Slam x t $ \z b -> f z (b ++ a)
action _ t = t

leftMap :: Integer -> Sem -> Sem
leftMap n = action (genericReplicate n Ld)

app :: Integer -> Ctx -> Sem -> Sem -> Sem
app n _ (Slam _ _ f) x = f n [] x

rec :: Integer -> Ctx -> Term -> Sem -> Sem -> Sem -> Sem
rec 0 _ _ z _ Szero = z
rec 0 c t z s (Ssuc p) = app 0 c (app 0 c s p) (rec 0 c t z s p)
rec n c t z s p | n > 0 = rec (n - 1) c t z s p
rec _ _ _ _ _ _ = error "rec: ERROR"

rename :: Term -> String -> String -> Term
rename q x r | x == r = q
rename Zero _ _ = Zero
rename Nat _ _ = Nat
rename Top _ _ = Top
rename Bot _ _ = Bot
rename Unit _ _ = Unit
rename Suc _ _ = Suc
rename q@(Type _) _ _ = q
rename (Var y) x r | x == y = Var r
rename q@(Var _) _ _ = q
rename (Refl t) x r = Refl (rename t x r)
rename (App a b) x r = App (rename a x r) (rename b x r)
rename q@(Lam y _ _) x _ | x == y = q
rename (Lam y t s) x r | y == r = let
    y' = head $ dropWhile (\z -> z == x || z == r) $ iterate (++ "'") y
    in Lam y' (rename t x r) $ rename (rename s y y') x r
rename (Lam y t s) x r = Lam y (rename t x r) (rename s x r)
rename (Id a) x r = Id (rename a x r)
rename (Pi t) x r = Pi (rename t x r)
rename (Cong t s) x r = Cong (rename t x r) (rename s x r)
rename (R t z s p) x r = R (rename t x r) (rename z x r) (rename s x r) (rename p x r)

eval :: Term -> Integer -> Ctx -> Sem
eval Zero _ _ = Szero
eval Nat _ _ = Snat
eval Top _ _ = Stop
eval Bot _ _ = Sbot
eval Unit _ _ = Sunit
eval (Type k) _ _ = Stype k
eval Suc _ _ = Slam "n" Snat $ \_ _ -> Ssuc
eval (Var x) _ c = fromMaybe (error $ "Unknown variable: " ++ x) (M.lookup x c)
eval (Refl t) n c = eval t n c
eval (App a b) n c = app n c (eval a n c) (eval b n c)
eval (Lam x t r) n c = Slam x (eval t n c) $ \k m s -> eval r k $ M.insert x s (M.map (action m) c)
eval (Id a) n c = Slam "b" Snat {- TODO: typeOf a -} $ \_ _ -> Sid (eval a n c)
eval (Pi t) n c = Spi (eval t n c)
eval (Cong t s) n c = case eval t n c of
    Slam _ _ f -> f (n + 1) [Ud] (eval s n c)
    _ -> error "eval: ERROR"
eval (R t z s p) n c = rec n c t (leftMap n $ eval z n c) (leftMap n $ eval s n c) (eval p n c)

---------------------------------------------------------------------------------------------------

nat :: Integer -> Term
nat 0 = Zero
nat n = Suc `App` nat (n - 1)

cR t = R (Lam "_" Nat t)
eqTest1 = Lam "x" Nat $ Lam "y" Nat $ Var "x" `App` Var "y"
eqTest2 = Lam "x" Nat $ Lam "x" Nat $ Var "x" `App` Var "x"
eqTest3 = Lam "z" Nat $ Lam "t" Nat $ Var "z" `App` Var "t"
omega = Lam "x" Nat $ Var "x" `App` Var "x"
one t = Lam "x" (t `arr` t) $ Lam "y" t $ Var "x" `App` Var "y"
i t = Lam "x" t (Var "x")
k = Lam "x" Nat $ Lam "y" Nat (Var "x")
-- alphaTest = App (one $ Nat `arr` Nat) (one Nat)
alphaTest = let t = Nat `arr` Nat in App
   (Lam "x" (t `arr` t) $ Lam "y" t $ Var "x" `App` Var "y")
   (Lam "x" (Nat `arr` Nat) $ Lam "y" Nat $ Var "x" `App` Var "y")
-- alphaTest = let t = Nat `arr` Nat in
--     Lam "y" t $ (Lam "x" (Nat `arr` Nat) $ Lam "y" Nat $ Var "x" `App` Var "y") `App` Var "y"
plus = Lam "x" Nat $ Lam "y" Nat $ cR Nat (Var "x") (k `App` Suc) (Var "y")
    -- \x y. R x (K suc) y
mul = Lam "x" Nat $ Lam "y" Nat $ cR Nat Zero (k `App` (plus `App` Var "x")) (Var "y")
    -- \x y. R 0 (K (plus x)) y
exp' = Lam "x" Nat $ Lam "y" Nat $ cR Nat (nat 1) (k `App` (mul `App` Var "x")) (Var "y")
    -- \x y. R 1 (K (mul x)) y
congTest1 = Lam "x" Nat $ cR Nat (Var "x") (k `App` Suc) (nat 0) -- \x. R x (K suc) 0
congTest2 = Lam "x" Nat $ plus `App` Var "x" `App` nat 3 -- \x. plus x 3
congTest3 = plus `App` nat 0
congTest4 = plus `App` nat 3
congTest5a = Lam "x" (Nat `arr` Nat) $ Lam "y" (Nat `arr` Nat) $ Lam "z" (Id (nat 0) `App` nat 1)
    $ Cong (Lam "t" Nat $ Var "x" `App` (Var "y" `App` Var "t")) (Var "z")
congTest5b = Lam "x" (Nat `arr` Nat) $ Lam "y" (Nat `arr` Nat) $ Lam "z" (Id (nat 0) `App` nat 1)
    $ Cong (Lam "t" Nat $ Var "x" `App` Var "y")
    $ (Cong (Lam "t" Nat $ Var "y" `App` Var "t") (Var "z"))

(~?/=) :: (Eq a, Show a) => a -> a -> Test
x ~?/= y = TestCase $ assertBool (show x ++ " shoud not be equal to " ++ show y) (x /= y)

main = putStrLn "OK"

{-
main = fmap (\_ -> ()) $ runTestTT $ test
    $    label "(==)"
    [ eqTest1 ~?= eqTest3
    , eqTest1 ~?/= eqTest2
    ] ++ label "alpha conversion"
    [ norm alphaTest ~?= one Nat
    ] ++ label "plus"
    [ norm (plus `App` nat 3 `App` nat 4) ~?= nat 7
    , norm (plus `App` nat 4 `App` nat 3) ~?= nat 7
    ] ++ label "mul"
    [ norm (mul `App` nat 3 `App` nat 4) ~?= nat 12
    , norm (mul `App` nat 4 `App` nat 3) ~?= nat 12
    ] ++ label "exp"
    [ norm (exp' `App` nat 3 `App` nat 4) ~?= nat 81
    , norm (exp' `App` nat 4 `App` nat 3) ~?= nat 64
    ] ++ label "cong"
    [ norm (Cong (i Nat) `App` Var "x") ~?= Var "x"
    , norm (Cong (i Nat) `App` nat 7) ~?= nat 7
    , norm (Cong congTest1 `App` Refl (nat 0)) ~?= Refl (nat 0)
    , norm (Cong congTest2 `App` Refl (nat 4)) ~?= Refl (nat 7)
    , norm (Cong congTest3 `App` Refl (nat 0)) ~?= Refl (nat 0)
    , norm (Cong congTest4 `App` Refl (nat 4)) ~?= Refl (nat 7)
--    , norm congTest5b ~?= congTest5b
--    , norm congTest5a ~?= congTest5b
    , norm congTest5a ~?= norm congTest5b
    ]
  where
    label :: String -> [Test] -> [Test]
    label l = map (\(i,t) -> TestLabel (l ++ " [" ++ show i ++ "]") t) . zip [1..]
-}
