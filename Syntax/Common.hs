module Syntax.Common
    ( Level(..)
    , parseLevel
    , freshName
    ) where

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

parseLevel :: String -> Level
parseLevel "Type" = Omega
parseLevel ('T':'y':'p':'e':s) = Finite (read s)
parseLevel s = error $ "parseLevel: " ++ s

freshName :: String -> [String] -> String
freshName "_" vars = freshName "x" vars
freshName base vars | elem base vars = go 0
                    | otherwise = base
  where
    go n | elem x vars = go (n + 1)
         | otherwise = x
         where x = base ++ show n
