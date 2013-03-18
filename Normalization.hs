import qualified Data.Map as M

infixl 5 `App`
data Term = Var String | Lam String Term (String -> Term) | App Term Term | Zero
    | Suc | R String (Term -> Term) Term Term Term | Top | Bot | Unit | Pi String Term (String -> Term)
    | Id Term Term | Refl Term | Repl Term | Cong Term | Nat

arr :: Term -> Term -> Term
arr a b = Pi "_" a (\_ -> b)

{-
typeOf :: M.Map String Term -> Term -> Maybe Term
typeOf m (Var x) = M.lookup x m
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
typeOf m (Refl x) = Just (Id x x)
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
        showArrow e@(Pi _ _ _) = show' True e
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
        show' par (Lam x t f) = addParens par $ "\\" ++ x ++ ":" ++ showArrow t ++ ". " ++ show (f x)
        show' par (App a b) = addParens par $ show a ++ " " ++ show' True b
        show' par (R x t z s n) = addParens par $ "R (\\" ++ x ++ ":Nat. " ++ show (t (Var x)) ++ ") "
            ++ show' True z ++ " " ++ show' True s ++ " " ++ show' True n
        show' par (Pi x t f) = addParens par $ "(" ++ x ++ " : " ++ show t ++ ") -> " ++ show (f x)
        show' par (Id a b) = addParens par $ show' True a ++ " = " ++ show' True b
        show' par (Refl x) = addParens par $ "refl " ++ show' True x
        show' par (Cong t) = addParens par $ "cong " ++ show' True t

-- data BaseMap = DegMap Integer | FaceMap Integer
-- type SimpMap = [BaseMap]
data Base = Tm Term | Fun String Term (Sem -> Sem)
type Sem = Integer -> Base
type Ctx = M.Map String Sem

{-
subst :: Base -> Base -> Base -> Base
subst c (Tm (Refl _ _)) e = e
subst (Fun _ f) p e = case f 1 p of
    Tm (Refl _ _) -> e
    -- Tm (Uni l r lr rl) -> app m (eval l m) e
    _ -> error "TODO"
subst c p e = error "TODO"

sym {a} p = subst (\c -> c = a) p (refl a) = repl (cong (\c -> c = a) p) (refl a)

subst (\X -> X) N-Z-iso 0
-}

app :: Ctx -> Base -> Sem -> Base
app _ (Fun _ _ f) x = f x 0
app m (Tm t) x = Tm $ t `App` reify (x 0) m

rec :: Ctx -> String -> (Term -> Term) -> Base -> Base -> Base -> Sem
rec _ _ _ _ _ _ n | n < 0 = error "ERROR: rec"
rec _ _ _ _ _ (Fun _ _ _) _ = error "ERROR"
rec m x t z s (Tm Zero) 0 = z
rec m x t z s (Tm (App Suc p)) 0 = app m (app m s (Tm . genRefl p)) (rec m x t z s (Tm p))
rec m x t z s (Tm (Refl p)) n | n > 0 = Tm $ Refl $ reify (rec m x t z s (Tm p) (n - 1)) m
rec m x t z s (Tm e) n = Tm $ genCong (Lam "e" Nat $ R x t (reify z m) (reify s m) . Var) n `App` e
    -- TODO: cong-dep

genRefl :: Term -> Integer -> Term
genRefl c n | n < 0 = error "ERROR: genRefl"
genRefl c 0 = c
genRefl c n = Refl (genRefl c (n - 1))

genRefl' :: Base -> Integer -> Base
genRefl' (Tm t) n = Tm (genRefl t n)
genRefl' (Fun x t f) n = Fun x t (\s k -> genRefl' (f s k) n)

genCong :: Term -> Integer -> Term
genCong c n | n < 0 = error "ERROR: genCong"
genCong c 0 = c
genCong c n = Cong $ genCong c (n - 1)

eval :: Term -> Ctx -> Sem
eval _ _ n | n < 0 = error "ERROR: eval"
eval Suc _ n = Fun "n" Nat $ \t k -> case t k of
    Tm t' -> Tm $ genRefl (genCong Suc k `App` t') n
    _ -> error "ERROR"
eval (R x t z s p) c n = if M.member x c
    then eval (R (x ++ "'") t z s p) c n
    else rec c x t (eval z c 0) (eval s c 0) (eval p c n) n
eval v@(Var x) c n = maybe (Tm v) (\s -> s n) (M.lookup x c)
eval (App a b) c n = app c (eval a c n) (eval b c)
eval (Lam x t f) c n = if M.member x c
    then eval (Lam (x ++ "'") t f) c n
    else Fun x (normCtx c t) $ \s -> eval (f x) (M.insert x s c)
eval (Cong t) c n = eval t c (n + 1) {- case eval t c 0 of
    Fun x t' f -> Fun x t' $ \s k -> genRefl' (f (s . succ) (succ k)) n
    _ -> error "ERROR" -}
eval (Refl t) c n = Tm $ genRefl (Refl $ norm t) n
eval Zero _ n = Tm (genRefl Zero n)
eval Nat _ n = Tm (genRefl Nat n)
eval Top _ n = Tm (genRefl Top n)
eval Bot _ n = Tm (genRefl Bot n)
eval Unit _ n = Tm (genRefl Unit n)
eval (Pi x t f) c n = if M.member x c
    then eval (Pi (x ++ "'") t f) c n
    else Tm $ genRefl (Pi x (normCtx c t) (normCtx c . f)) n
eval (Id a b) c n = Tm $ genRefl (Id (normCtx c a) (normCtx c b)) n
    -- TODO: check if 'a' and 'b' have function type

nat :: Integer -> Term
nat 0 = Zero
nat n = Suc `App` nat (n - 1)

reify :: Base -> Ctx -> Term
reify (Tm t) _ = t
reify (Fun x t f) m = if M.member x m
    then reify (Fun (x ++ "'") t f) m
    else Lam x t $ \x -> let s = f (Tm . genRefl (Var x)) 0 in reify s (M.insert x (const s) m)

normCtx :: Ctx -> Term -> Term
normCtx c t = reify (eval t c 0) c

norm :: Term -> Term
norm = normCtx M.empty

omega = Lam "x" Nat $ \x -> Var x `App` Var x
one = Lam "x" (Nat `arr` Nat) $ \x -> Lam "y" Nat $ \y -> Var x `App` Var y
i = Lam "x" Nat Var
k = Lam "x" Nat $ \x -> Lam "y" Nat $ \y -> Var x
test2 = App one one
cR t = R "_" (\_ -> t)
plus = Lam "x" Nat $ \x -> Lam "y" Nat $ cR Nat (Var x) (k `App` Suc) . Var
    -- \x y. R x (K suc) y
mul = Lam "x" Nat $ \x -> Lam "y" Nat $ cR Nat Zero (k `App` (plus `App` Var x)) . Var
    -- \x y. R 0 (K (plus x)) y
exp' = Lam "x" Nat $ \x -> Lam "y" Nat $ cR Nat (nat 1) (k `App` (mul `App` Var x)) . Var
    -- \x y. R 1 (K (mul x)) y

main = do
    print (norm test2)
    print $ norm $ exp' `App` nat 3 `App` nat 4
    print $ norm $ Cong (plus `App` nat 0) `App` Refl (nat 0)
