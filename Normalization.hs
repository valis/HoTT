module Normalization where

import qualified Data.Map as M
import Test.HUnit
import Data.List
import Data.Maybe

infixl 5 `App`
data Term = Var String | Lam String Term Term | App Term Term | Zero | Proj1 Term | Proj2 Term
    | Suc | R Term Term Term Term | Top | Bot | Unit | Pi Term | Sigma Term
    | Id Term Term | Refl Term | Cong Term Term | Nat | Type Integer | Repl Term
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
        eq n (Id t s) (Id t' s') = eq n t t' && eq n s s'
        eq n (App t s) (App t' s') = eq n t t' && eq n s s'
        eq n (Lam x t s) (Lam x' t' s') = eq n t t' &&
            eq (n + 1) (rename s x (' ':show n)) (rename s' x' (' ':show n))
        eq n (Pi t) (Pi t') = eq n t t'
        eq n (R t z s p) (R t' z' s' p') = eq n t t' && eq n z z' && eq n s s' && eq n p p'
        eq n (Repl t) (Repl t') = eq n t t'
        eq n (Proj1 t) (Proj1 t') = eq n t t'
        eq n (Proj2 t) (Proj2 t') = eq n t t'
        eq n (Sigma t) (Sigma t') = eq n t t'
        eq _ _ _ = False

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
        show' par (Lam x t s) = addParens par $ "λ" ++ x ++ ":" ++ showArrow t ++ ". " ++ show s
        show' par (Id a b) = addParens par $ show' True a ++ " = " ++ show' True b
        show' par (App a b) = addParens par $ show a ++ " " ++ show' True b
        show' par (R t z s n) = addParens par $
            "R " ++ show' True t ++ " " ++ show' True z ++ " " ++ show' True s ++ " " ++ show' True n
        show' par (Pi (Lam "_" t s)) = addParens par $ show' True t ++ " → " ++ show s
        show' par (Pi (Lam x t s)) = addParens par $ "(" ++ x ++ " : " ++ show t ++ ") → " ++ show s
        show' par (Pi _) = error "show: Π without λ"
        show' par (Refl x) = addParens par $ "refl " ++ show' True x
        show' par (Cong t s) = addParens par $ "cong " ++ show' True t ++ " " ++ show' True s
        show' par (Repl t) = addParens par $ "repl " ++ show' True t
        show' par (Sigma (Lam "_" t s)) = addParens par $ show' True t ++ " × " ++ show' True s
        show' par (Sigma (Lam x t s)) = addParens par $
            "Σ(" ++ x ++ " : " ++ show' True t ++ ") " ++ show' True s
        show' par (Sigma _) = error "show: Σ without λ"
        show' par (Proj1 t) = addParens par $ "proj₁ " ++ show' True t
        show' par (Proj2 t) = addParens par $ "proj₂ " ++ show' True t

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
rename (Id a b) x r = Id (rename a x r) (rename b x r)
rename (Pi t) x r = Pi (rename t x r)
rename (Cong t s) x r = Cong (rename t x r) (rename s x r)
rename (R t z s p) x r = R (rename t x r) (rename z x r) (rename s x r) (rename p x r)
rename (Repl t) x r = Repl (rename t x r)
rename (Sigma t) x r = Sigma (rename t x r)
rename (Proj1 t) x r = Proj1 (rename t x r)
rename (Proj2 t) x r = Proj2 (rename t x r)

data D = Ld | Rd | Ud deriving (Eq, Show)
type GlobMap = [D]
data Sem
    = Slam String Sem (Integer -> GlobMap -> Sem -> Sem) -- Constructor for Pi-types
    | Szero | Ssuc Sem -- Constructors for Nat
    | Sunit -- Constructor for Top
    | Sprod Sem Sem -- Constructor for Sigma
    | Spi Sem | Ssigma Sem | Stop | Snat | Sbot | Sid Sem Sem | Stype Integer -- Constructors for Type_k
    | Siso Sem Sem Sem Sem -- | Strans Sem Sem | Ssym Sem
    | Svar String | Sapp Sem Sem | Srec Sem Sem Sem | Sproj1 Sem | Sproj2 Sem | Srepl Sem | Srefl Sem
    | Sup Sem Sem Sem | UnknownOfType Sem
type Ctx = M.Map String Sem

instance Eq Sem where
    (==) = eq 0
      where
        eqAction [] [] = True
        eqAction (Ud : Ld : xs) ys = eqAction xs ys
        eqAction (Ud : Rd : xs) ys = eqAction xs ys
        eqAction xs (Ud : Ld : ys) = eqAction xs ys
        eqAction xs (Ud : Rd : ys) = eqAction xs ys
        eqAction (Ld : Ld : xs) (Rd : Ld : ys) = xs == ys
        eqAction (Ld : Rd : xs) (Rd : Rd : ys) = xs == ys
        eqAction (x:xs) (y:ys) = x == y && xs == ys
        eqAction _ _ = False
        
        eq n (Slam _ t s) (Slam _ t' s') = eq n t t' &&
            eq (n + 1) (s 0 [] $ Svar $ "x_" ++ show n) (s' 0 [] $ Svar $ "x_" ++ show n)
        eq _ Szero Szero = True
        eq n (Ssuc t) (Ssuc t') = eq n t t'
        eq _ Sunit Sunit = True
        eq n (Spi t) (Spi t') = eq n t t'
        eq _ Snat Snat = True
        eq _ Stop Stop = True
        eq _ Sbot Sbot = True
        eq n (Sid a b) (Sid a' b') = eq n a a' && eq n b b'
        eq _ (Stype k) (Stype k') = k == k'
        eq _ (Svar x) (Svar x') = x == x'
        eq n (Sapp t s) (Sapp t' s') = eq n t t' && eq n s s'
        eq n (Srec t s p) (Srec t' s' p') = eq n t t' && eq n s s' && eq n p p'
        eq n (Sup _ _ t) (Sup _ _ t') = eq n t t'
        eq n (Ssigma t) (Ssigma t') = eq n t t'
        eq n (Sproj1 t) (Sproj1 t') = eq n t t'
        eq n (Sproj2 t) (Sproj2 t') = eq n t t'
        eq n (Sprod t s) (Sprod t' s') = eq n t t' && eq n s s'
        eq n (Srepl t) (Srepl t') = eq n t t'
        eq n (Siso f g p q) (Siso f' g' p' q') = eq n f f' && eq n g g' && eq n p p' && eq n q q'
        eq n (Srefl t) (Srefl t') = eq n t t'
        eq n (UnknownOfType t) (UnknownOfType t') = eq n t t'
        eq _ _ _ = False

instance Show Sem where
    show = show' 0 False
      where
        addParens True s = "(" ++ s ++ ")"
        addParens False s = s
        
        showArrow n e@(Slam _ _ _) = show' n True e
        showArrow n e@(Spi _) = show' n True e
        showArrow n e = show' n False e
        
        show' _ _ x | Just p <- getNat x = show p
          where getNat Szero = Just 0
                getNat (Ssuc x) = fmap succ (getNat x)
                getNat _ = Nothing
        show' _ _ (Svar x) = x
        show' n par (Ssuc p) = addParens par $ "S " ++ show' n True p
        show' _ _ Stop = "Top"
        show' _ _ Sbot = "Bot"
        show' _ _ Sunit = "Unit"
        show' _ _ Snat = "Nat"
        show' _ _ (Stype k) = "Type_" ++ show k
        show' n par (Sid a b) = addParens par $ show' n True a ++ " = " ++ show' n True b
        show' n par (Spi (Slam "_" t s)) = addParens par $
            show' n True t ++ " -> " ++ show' n False (s 0 [] (error "Show Sem"))
        show' n par (Spi (Slam x t s)) = addParens par $ "(" ++ x ++ " : " ++ show' n False t
            ++ ") -> " ++ show' (n + 1) False (s 0 [] $ Svar $ "x_" ++ show n)
        show' _ _ (Spi _) = error "show: Pi without Lam"
        show' n par (Sapp a b) = addParens par $ show' n False a ++ " " ++ show' n True b
        show' n par (Srec z s p) = addParens par $
            "R " ++ show' n True z ++ " " ++ show' n True s ++ " " ++ show' n True p
        show' n par (Slam _ t s) = addParens par $ "\\x_" ++ show n ++ ":" ++ showArrow n t
            ++ ". " ++ show' (n + 1) False (s 0 [] $ Svar $ "x_" ++ show n)
        show' n par (Sup _ _ t) = show' n par t
        show' n par (Ssigma (Slam "_" t s)) = addParens par $
            show' n True t ++ " × " ++ show' n True (s 0 [] (error "Show Sem"))
        show' n par (Ssigma (Slam x t s)) = addParens par $ "Σ(x_" ++ show n ++ " : "
            ++ show' n True t ++ ") " ++ show' (n + 1) True (s 0 [] $ Svar $ "x_" ++ show n)
        show' _ _ (Ssigma _) = error "show: Σ without λ"
        show' n par (Sproj1 t) = addParens par $ "proj₁ " ++ show' n True t
        show' n par (Sproj2 t) = addParens par $ "proj₂ " ++ show' n True t
        show' n par (Sprod t s) = addParens par $ show' n True t ++ ", " ++ show' n False s
        show' n par (Srepl t) = addParens par $ "repl " ++ show' n True t
        show' n par (Siso f g p q) = addParens par $ "iso " ++ show' n True f
            ++ " " ++ show' n True g ++ " " ++ show' n True p ++ " " ++ show' n True q
        show' n par (Srefl t) = addParens par $ "refl " ++ show' n True t

action :: GlobMap -> Sem -> Sem
action [] t = t
action a (Slam x t f) = Slam x t $ \z b -> f z (b ++ a)
action a (Sprod t s) = Sprod (action a t) (action a s)
action _ Szero = Szero
action _ t@(Ssuc _) = t
action _ Sunit = Sunit
action (Ud:as) t | isType t = action as $ Sup t t (Siso f f p p)
  where f = Slam "x" t $ \_ _ -> id
        p = Slam "x" (UnknownOfType (Sid t t)) $ \_ _ -> id
        isType Snat = True
        isType Stop = True
        isType Sbot = True
        isType (Stype _) = True
        isType (Ssigma _) = True
        isType (Spi _) = True
        isType (Sid _ _) = True
        isType _ = False
action (Ud:as) t@(Siso f _ _ _) = action as $ Sup t t (action [Ud] f)
action (Ld:as) (Sup l _ _) = l
action (Rd:as) (Sup _ r _) = r
action (Ud:as) t@(Sup _ _ s) = action as $ Sup t t (action [Ud] s)
action (Ud:as) t@(Svar _) = action as (Srefl t)
action as (Sapp t s) = Sapp (action as t) (action as s)
action as (Srec z s p) = Srec (action as z) (action as s) (action as p)
action as (Sproj1 t) = Sproj1 (action as t)
action as (Sproj2 t) = Sproj2 (action as t)
action as (Srepl t) = Srepl (action as t)
action (Ud:as) t@(Srefl _) = action as (Srefl t)
action (Ld:as) (Srefl t) = t
action (Rd:as) (Srefl t) = t
action _ _ = error "action: ERROR"

app :: Integer -> Sem -> Sem -> Sem
app n (Slam _ _ f) x = f n [] x
app _ t x = Sapp t x

rec :: Integer -> Sem -> Sem -> Sem -> Sem
rec n z _ Szero = z
rec n z s (Ssuc p) = app n (app n s p) (rec n z s p)
rec _ z s p = Srec z s p

proj1 :: Integer -> Sem -> Sem
proj1 _ (Sprod x _) = x
proj1 _ t = Sproj1 t

proj2 :: Integer -> Sem -> Sem
proj2 _ (Sprod _ y) = y
proj2 _ t = Sproj2 t

{-
sym :: Integer -> Sem -> Sem
sym 0 (Sup a b (Siso f g p q)) = Sup b a (Siso g f q p)
sym n (Sprod x y) = undefined -- Sprod (sym n x) (sym n y)
    -- (x,y) |-> (sym x, cong (subst B (sym x)) (sym y))
sym n (Slam x t s) = Slam x t $ \k _ y -> sym k y
sym n t = Ssym t
-}

repl :: Integer -> Sem -> Sem
repl 0 (Siso f _ _ _) = f
repl n (Sup _ _ t) | n > 0 = repl (n - 1) t
repl _ t = Srepl t

eval :: Term -> Integer -> Ctx -> Sem
eval Top n _ = action (genericReplicate n Ud) Stop
eval Nat n _ = action (genericReplicate n Ud) Snat
eval Bot n _ = action (genericReplicate n Ud) Sbot
eval (Type k) n _ = action (genericReplicate n Ud) (Stype k)
{-
eval (Sigma t) 0 c = Ssigma (eval t 0 c)
eval (Sigma (Lam z t s)) 1 c = let
    cl = M.map (action [Ld]) c
    cr = M.map (action [Rd]) c
    pl = eval p 0 cl
    pr = eval p 0 cr
    tl = eval t 0 cl
    tr = eval t 0 cr
    Siso tf tg tp tq = eval t 1 c
    rf = Slam "x" pl $ \kx mx x -> let
        Siso sf sg sp sq = eval s (kx + 1) (M.insert z (action [Ud] (app kx (action mx tf) (proj1 x))) c)
        in 
    in Siso rf rg rp rq
-}
eval (Sigma t) 0 c = Ssigma (eval t 0 c)
eval (Sigma t) n c = error "eval: TODO: Sigma"
eval (Pi t) 0 c = Spi (eval t 0 c)
eval (Pi t) n c = error "eval: TODO: Pi"
eval (Id a b) 0 c = Sid (eval a 0 c) (eval b 0 c)
eval (Id a b) n c = error "eval: TODO: Id"
eval Zero _ _ = Szero
eval Unit _ _ = Sunit
eval Suc _ _ = Slam "n" Snat $ \_ _ -> Ssuc
eval (Var x) _ c = fromMaybe (error $ "Unknown variable: " ++ x) (M.lookup x c)
eval (Refl t) n c = eval t (n + 1) (M.map (action [Ud]) c)
eval (App a b) n c = app n (eval a n c) (eval b n c)
eval (Lam x t r) n c = Slam x (uot n c) $ \k m s -> eval r k $ M.insert x s (M.map (action m) c)
  where uot 0 c = eval t 0 c
        uot n c = Sid (uot (n - 1) (M.map (action [Ld]) c)) (uot (n - 1) (M.map (action [Rd]) c))
eval (Cong t s) n c = app (n + 1) (action [Ud] (eval t n c)) (eval s n c)
eval (R _ z s p) n c = rec n (eval z n c) (eval s n c) (eval p n c)
eval (Repl t) n c = repl n (eval t n c)
eval (Proj1 t) n c = proj1 n (eval t n c)
eval (Proj2 t) n c = proj2 n (eval t n c)

---------------------------------------------------------------------------------------------------

norm :: Term -> Sem
norm t = eval t 0 M.empty

nat :: Integer -> Term
nat 0 = Zero
nat n = Suc `App` nat (n - 1)

snat :: Integer -> Sem
snat 0 = Szero
snat n = Ssuc $ snat (n - 1)

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
exp' = Lam "x" Nat $ Lam "y" Nat $ cR Nat (Suc `App` Zero) (k `App` (mul `App` Var "x")) (Var "y")
    -- \x y. R 1 (K (mul x)) y
congTest1 = Lam "x" Nat $ cR Nat (Var "x") (k `App` Suc) (nat 0) -- \x. R x (K suc) 0
congTest2 = Lam "x" Nat $ plus `App` Var "x" `App` nat 3 -- \x. plus x 3
congTest3 = plus `App` nat 0
congTest4 = plus `App` nat 3
congTest5a = Lam "x" (Nat `arr` Nat) $ Lam "y" (Nat `arr` Nat) $ Lam "z" (Id (nat 0) (nat 1))
    $ Cong (Lam "t" Nat $ Var "x" `App` (Var "y" `App` Var "t")) (Var "z")
congTest5b = Lam "x" (Nat `arr` Nat) $ Lam "y" (Nat `arr` Nat) $ Lam "z" (Id (nat 0) (nat 1))
    $ Cong (Lam "t" Nat $ Var "x" `App` Var "t")
    $ (Cong (Lam "t" Nat $ Var "y" `App` Var "t") (Var "z"))
recTest1 = Lam "X" (Type 0) $ Lam "z" (Var "X") $ Lam "s" (Nat `arr` Var "X" `arr` Var "X") $
    Lam "n" Nat $ Refl $ R (Lam "_" Nat (Var "X")) (Var "z") (Var "s") (Var "n")
recTest2 = Lam "X" (Type 0) $ Lam "z" (Var "X") $ Lam "s" (Nat `arr` Var "X" `arr` Var "X") $
    Lam "n" Nat $ Cong (Lam "m" Nat $ R (Lam "_" Nat (Var "X")) (Var "z") (Var "s") (Var "m")) (Refl (Var "n"))

(~?/=) :: (Eq a, Show a) => a -> a -> Test
x ~?/= y = TestCase $ assertBool (show x ++ " shoud not be equal to " ++ show y) (x /= y)

main = fmap (\_ -> ()) $ runTestTT $ test
    $    label "(==)"
    [ eqTest1 ~?= eqTest3
    , eqTest1 ~?/= eqTest2
    ] ++ label "alpha conversion"
    [ norm alphaTest ~?= norm (one Nat)
    ] ++ label "plus"
    [ norm (plus `App` nat 3 `App` nat 4) ~?= snat 7
    , norm (plus `App` nat 4 `App` nat 3) ~?= snat 7
    ] ++ label "mul"
    [ norm (mul `App` nat 3 `App` nat 4) ~?= snat 12
    , norm (mul `App` nat 4 `App` nat 3) ~?= snat 12
    ] ++ label "exp"
    [ norm (exp' `App` nat 3 `App` nat 4) ~?= snat 81
    , norm (exp' `App` nat 4 `App` nat 3) ~?= snat 64
    ] ++ label "cong"
    [ norm (Cong (i Nat) (nat 7)) ~?= snat 7
    , norm (Cong congTest1 (Refl (nat 0))) ~?= snat 0
    , norm (Cong congTest2 (Refl (nat 4))) ~?= snat 7
    , norm (Cong congTest3 (Refl (nat 0))) ~?= snat 0
    , norm (Cong congTest4 (Refl (nat 4))) ~?= snat 7
    , norm congTest5a ~?= norm congTest5b
    ] ++ label "rec"
    [ norm recTest1 ~?= norm recTest2
    ]
  where
    label :: String -> [Test] -> [Test]
    label l = map (\(i,t) -> TestLabel (l ++ " [" ++ show i ++ "]") t) . zip [1..]
