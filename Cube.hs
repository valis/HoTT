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
    , isDeg, signAt, lastFace, commonDeg
    ) where

import Data.List

data Sign = Plus | Minus | Zero deriving Eq
newtype Cube a = Cube { unCube :: FaceMap -> a }
data CubeMap = CubeMap { degs :: DegMap, faces :: FaceMap } deriving Eq
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

instance Show FaceMap where
    show (FaceMap f) = map signToChar f

instance Show DegMap where
    show (DegMap d) = map (\b -> if b then '1' else '0') d

instance Show CubeMap where
    show (CubeMap d f) = show d ++ "." ++ show f

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
    go [] ds = ds

composefd :: FaceMap -> DegMap -> CubeMap
composefd (FaceMap []) (DegMap []) = CubeMap (DegMap []) (FaceMap [])
composefd (FaceMap (f:fs)) (DegMap (d:ds)) =
    let CubeMap (DegMap ds') (FaceMap fs') = composefd (FaceMap fs) (DegMap ds)
    in CubeMap (DegMap $ if f == Zero then d:ds' else ds') (FaceMap $ if d then f:fs' else fs')
composefd (FaceMap []) d = cubeMapd d
composefd f d = error $ "composefd " ++ show f ++ "," ++ show d

composec :: CubeMap -> CubeMap -> CubeMap
composec (CubeMap d1 f1) (CubeMap d2 f2) =
    let CubeMap d f = composefd f1 d2
    in CubeMap (composed d1 d) (composef f f2)

cubeMapf :: FaceMap -> CubeMap
cubeMapf f = CubeMap (idd $ domf f) f

cubeMapd :: DegMap -> CubeMap
cubeMapd d = CubeMap d (idf $ codd d)

isDeg :: DegMap -> Integer -> Bool
isDeg (DegMap []) _ = False
isDeg (DegMap (d:_)) 0 = not d
isDeg (DegMap (_:ds)) n = isDeg (DegMap ds) (n - 1)

signAt :: FaceMap -> Integer -> Sign
signAt (FaceMap ds) k = ds `genericIndex` k

lastFace :: FaceMap -> (FaceMap,Sign)
lastFace (FaceMap []) = error "lastFace"
lastFace (FaceMap [s]) = (FaceMap [], s)
lastFace (FaceMap (s:ss)) =
    let (FaceMap ss', l) = lastFace (FaceMap ss)
    in (FaceMap (s:ss'), l)

-- commonDeg (x : a -> c) (y : a -> d) (k < a) : (r : a -> b, t : b -> c, s : b -> d, k' < b)
-- composed r t == x, composed r s == y
commonDeg :: DegMap -> DegMap -> Integer -> (DegMap, DegMap, DegMap, Integer)
commonDeg (DegMap []) (DegMap []) k = (DegMap [], DegMap [], DegMap [], k)
commonDeg (DegMap (d:ds)) (DegMap (d':ds')) k =
    let (DegMap r, DegMap t, DegMap s, k') = commonDeg (DegMap ds) (DegMap ds') (k - 1)
    in if d || d'
        then (DegMap (True:r), DegMap (d:t), DegMap (d':s), if k == 0 then 0 else k' + 1)
        else (DegMap (False:r), DegMap t, DegMap s, if k == 0 then 0 else k')
commonDeg _ _ _ = error "commonDeg"
