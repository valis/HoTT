module Cube
    ( Cube, CubeMap, Sign(..)
    , face, caction, dom, compose, idc, isId
    , faceMap, degMap
    ) where

import Data.List

data Sign = Plus | Minus deriving Show
newtype Cube a = Cube (String -> a)
data CubeMap = CubeMap Integer [CubeMapGen] deriving Show
data CubeMapGen = Face Integer Sign | Deg Integer deriving Show

caction :: CubeMap -> Cube a -> Cube a
caction = undefined

idc :: Integer -> CubeMap
idc n = CubeMap n []

isId :: CubeMap -> Bool
isId (CubeMap _ s) = null s

compose :: CubeMap -> CubeMap -> CubeMap
compose (CubeMap d m1) (CubeMap _ m2) = CubeMap d (m1 ++ m2)

faceMap :: Integer -> Integer -> Sign -> CubeMap
faceMap n k s = CubeMap n [Face k s]

degMap :: Integer -> Integer -> CubeMap
degMap n k = CubeMap n [Deg k]

dom :: CubeMap -> Integer
dom (CubeMap d _) = d

interior :: Integer -> Cube a -> a
interior n (Cube c) = c (genericReplicate n '0')

signToChar :: Sign -> Char
signToChar Plus = '+'
signToChar Minus = '-'

face :: Integer -> Sign -> Cube a -> Cube a
face n s (Cube c) = Cube $ \x ->
    let (a,b) = genericSplitAt n x
    in c $ a ++ [signToChar s] ++ b
