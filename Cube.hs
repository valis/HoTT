module Cube
    ( Cube(..), Sign(..), CubeMap, DegMap, FaceMap
    , faces, degs, faceMap, degMap
    , idf, idd, idc
    , isIdc, isIdf, isIdd
    , isFaceMap, isDegMap
    , domf, domd, domc
    , codf, codd, codc
    , composef, composed, composefd, composec
    , cubeMapf, cubeMapd
    , isDeg
    ) where

import Data.List

data Sign = Plus | Minus | Zero deriving Eq
newtype Cube a = Cube { unCube :: FaceMap -> a }
data CubeMap = CubeMap { degs :: DegMap, faces :: FaceMap }
newtype FaceMap = FaceMap [Sign] deriving Eq
newtype DegMap = DegMap [Bool] deriving Eq

faceMap :: [Sign] -> FaceMap
faceMap = FaceMap

degMap :: [Bool] -> DegMap
degMap = DegMap

signToChar :: Sign -> Char
signToChar Plus = '+'
signToChar Minus = '-'
signToChar Zero = '0'

instance Show Sign where
    show s = [signToChar s]

instance Show CubeMap where
    show (CubeMap (DegMap d) (FaceMap f)) = map (\b -> if b then '1' else '0') d ++ "." ++ map signToChar f

idf :: Integer -> FaceMap
idf n = FaceMap (genericReplicate n Zero)

idd :: Integer -> DegMap
idd n = DegMap (genericReplicate n True)

idc :: Integer -> CubeMap
idc n = CubeMap (idd n) (idf n)

isIdf :: FaceMap -> Bool
isIdf (FaceMap f) = all (== Zero) f

isIdd :: DegMap -> Bool
isIdd (DegMap d) = and d

isIdc :: CubeMap -> Bool
isIdc (CubeMap d f) = isIdd d && isIdf f

isFaceMap :: CubeMap -> Bool
isFaceMap = isIdd . degs

isDegMap :: CubeMap -> Bool
isDegMap = isIdf . faces

domf :: FaceMap -> Integer
domf (FaceMap f) = genericLength $ filter (== Zero) f

domd :: DegMap -> Integer
domd (DegMap d) = genericLength d

domc :: CubeMap -> Integer
domc (CubeMap d _) = domd d

codf :: FaceMap -> Integer
codf (FaceMap f) = genericLength f

codd :: DegMap -> Integer
codd (DegMap d) = genericLength (filter id d)

codc :: CubeMap -> Integer
codc (CubeMap _ f) = codf f

composef :: FaceMap -> FaceMap -> FaceMap
composef (FaceMap fs1) (FaceMap fs2) = FaceMap (go fs1 fs2)
  where
    go (f1:fs1) (Zero:fs2) = f1 : go fs1 fs2
    go [] (Zero:_) = error "composef.1"
    go fs1 (f2:fs2) = f2 : go fs1 fs2
    go [] [] = []
    go _ [] = error "composef.2"

composed :: DegMap -> DegMap -> DegMap
composed (DegMap ds1) (DegMap ds2) = DegMap (go ds1 ds2)
  where
    go (True:ds1) (d2:ds2) = d2 : go ds1 ds2
    go (True:ds1) [] = error "composed.1"
    go (False:ds1) ds2 = False : go ds1 ds2
    go [] [] = []
    go [] _ = error "composed.2"

composefd :: FaceMap -> DegMap -> CubeMap
composefd (FaceMap []) (DegMap []) = CubeMap (DegMap []) (FaceMap [])
composefd (FaceMap (f:fs)) (DegMap (d:ds)) =
    let CubeMap (DegMap ds') (FaceMap fs') = composefd (FaceMap fs) (DegMap ds)
    in CubeMap (DegMap $ if f == Zero then d:ds' else ds') (FaceMap $ if d then f:fs' else fs')
composefd _ _ = error "composefd"

composec :: CubeMap -> CubeMap -> CubeMap
composec (CubeMap d1 f1) (CubeMap d2 f2) =
    let CubeMap d f = composefd f1 d2
    in CubeMap (composed d1 d) (composef f f2)

cubeMapf :: FaceMap -> CubeMap
cubeMapf (FaceMap f) = CubeMap (DegMap $ genericReplicate (genericLength $ filter (== Zero) f :: Integer) True) (FaceMap f)

cubeMapd :: DegMap -> CubeMap
cubeMapd (DegMap d) = CubeMap (DegMap d) $ FaceMap $ genericReplicate (genericLength $ filter id d :: Integer) Zero

isDeg :: DegMap -> Integer -> Bool
isDeg (DegMap []) _ = False
isDeg (DegMap (d:_)) 0 = not d
isDeg (DegMap (_:ds)) n = isDeg (DegMap ds) (n - 1)
