module Cube
    ( Cube(..), Sign(..), CubeMap, DegMap, FaceMap
    , faces, degs, faceMap, degMap, conMap
    , idf, idd, idc
    , isIdc, isIdf, isIdd
    , isFaceMap, isDegMap
    , domf, domd, domc
    , codf, codd, codc
    , liftf, liftd, liftc
    , composef, composed, composefd, composec
    , cubeMapf, cubeMapd, cubeMapc
    , isDeg, signAt, lastFace, getFace
    -- , commonDeg
    ) where

import Data.List

data Sign = Plus | Minus | Zero deriving Eq
newtype Cube a = Cube { unCube :: FaceMap -> a }
data CubeMap = CubeMap { degs :: DegMap, faces :: FaceMap } deriving Eq
newtype FaceMap = FaceMap [Sign] deriving Eq
data DegMap = DegMap [Bool] Integer deriving Eq

faceMap :: [Sign] -> FaceMap
faceMap = FaceMap

degMap :: [Bool] -> DegMap
degMap ds = DegMap ds 0

conMap :: Integer -> DegMap
conMap n = DegMap (genericReplicate (n + 1) True) 1

signToChar :: Sign -> Char
signToChar Plus = '+'
signToChar Minus = '-'
signToChar Zero = '0'

instance Show Sign where
    show s = [signToChar s]

instance Show FaceMap where
    show (FaceMap f) = map signToChar f

instance Show DegMap where
    show (DegMap d 0) = map (\b -> if b then '1' else '0') d
    show (DegMap d n) = map (\b -> if b then '1' else '0') d ++ "/" ++ show n

instance Show CubeMap where
    show (CubeMap d f) = show d ++ "." ++ show f

idf :: Integer -> FaceMap
idf n = FaceMap (genericReplicate n Zero)

idd :: Integer -> DegMap
idd n = DegMap (genericReplicate n True) 0

idc :: Integer -> CubeMap
idc n = CubeMap (idd n) (idf n)

isIdf :: FaceMap -> Bool
isIdf (FaceMap f) = all (== Zero) f

isIdd :: DegMap -> Bool
isIdd (DegMap d n) = n == 0 && and d

isIdc :: CubeMap -> Bool
isIdc (CubeMap d f) = isIdd d && isIdf f

isFaceMap :: CubeMap -> Bool
isFaceMap = isIdd . degs

isDegMap :: CubeMap -> Bool
isDegMap = isIdf . faces

domf :: FaceMap -> Integer
domf (FaceMap f) = genericLength $ filter (== Zero) f

domd :: DegMap -> Integer
domd (DegMap d _) = genericLength d

domc :: CubeMap -> Integer
domc (CubeMap d _) = domd d

codf :: FaceMap -> Integer
codf (FaceMap f) = genericLength f

codd :: DegMap -> Integer
codd (DegMap d n) = genericLength (filter id d) - n

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

composecd :: Integer -> DegMap -> DegMap
composecd n1 (DegMap [] 0) = DegMap (genericReplicate n1 True) n1
composecd n1 (DegMap (d:ds) n2) = DegMap (genericReplicate (n1 + 1) d ++ ds) $ if d then n1 + n2 else n2
composecd _ _ = error "composecd"

composed :: DegMap -> DegMap -> DegMap
composed (DegMap d1 n1) d2 =
    let DegMap d n = composecd n1 d2
    in DegMap (go d1 d) n
  where
    go (True:ds1) (d2:ds2) = d2 : go ds1 ds2
    go (True:ds1) [] = error "composed.1"
    go (False:ds1) ds2 = False : go ds1 ds2
    go [] [] = []
    go [] _ = error "composed.2"

composefd :: FaceMap -> DegMap -> CubeMap
composefd (FaceMap f) (DegMap d n) = composefc facemap n
  where
    CubeMap degmap facemap = go f d
    
    go [] [] = CubeMap (DegMap [] 0) (FaceMap [])
    go (f:fs) (d:ds) =
        let CubeMap (DegMap ds' _) (FaceMap fs') = go fs ds
        in CubeMap (DegMap (if f == Zero then d:ds' else ds') 0) (FaceMap $ if d then f:fs' else fs')
    go _ _ = error "composefd"
    
    conf1 (FaceMap []) = error "composec.conf1"
    conf1 (FaceMap [_]) = (Left False, FaceMap [])
    conf1 (FaceMap (Plus:fs)) = (Left False, FaceMap fs)
    conf1 (FaceMap (Zero:Plus:fs)) = (Left False, FaceMap (Zero:fs))
    conf1 (FaceMap (Zero:Zero:fs)) = (Left True, FaceMap (Zero:fs))
    conf1 (FaceMap (Minus:f:fs)) | f /= Zero = (Left False, FaceMap (Minus:fs))
    conf1 (FaceMap (_:_:fs)) = (Right $ DegMap (False : genericReplicate (domf $ FaceMap fs) True) 0, FaceMap (Minus:fs))
    
    composefc f 0 = CubeMap degmap f
    composefc f r =
        let (l,f1) = conf1 f
            CubeMap d2 f2 = composefc f1 (r - 1)
        in case l of
            Right d1 -> CubeMap (composed d1 d2) f2
            Left False -> CubeMap d2 f2
            Left True -> CubeMap (composecd 1 d2) f2

composec :: CubeMap -> CubeMap -> CubeMap
composec (CubeMap d1 f1) (CubeMap d2 f2) =
    let CubeMap d f = composefd f1 d2
    in CubeMap (composed d1 d) (composef f f2)

liftf :: FaceMap -> FaceMap
liftf (FaceMap f) = FaceMap (f ++ [Zero])

liftd :: DegMap -> DegMap
liftd (DegMap d n) = DegMap (d ++ [True]) n

liftc :: CubeMap -> CubeMap
liftc (CubeMap d f) = CubeMap (liftd d) (liftf f)

cubeMapf :: FaceMap -> CubeMap
cubeMapf f = CubeMap (idd $ domf f) f

cubeMapd :: DegMap -> CubeMap
cubeMapd d = CubeMap d (idf $ codd d)

cubeMapc :: DegMap -> FaceMap -> CubeMap
cubeMapc = CubeMap

isDeg :: DegMap -> Integer -> Bool
isDeg (DegMap [] _) _ = False
isDeg (DegMap (d:_) _) 0 = not d
isDeg (DegMap (_:ds) k) n = isDeg (DegMap ds k) (n - 1)

signAt :: FaceMap -> Integer -> Sign
signAt (FaceMap ds) k = ds `genericIndex` k

getFace :: FaceMap -> Integer -> ([Sign],Sign,[Sign])
getFace (FaceMap []) _ = error "getFace"
getFace (FaceMap (s:ss)) 0 = ([], s, ss)
getFace (FaceMap (s:ss)) n =
    let (s1, r, s2) = getFace (FaceMap ss) (n - 1)
    in (s:s1, r, s2)

lastFace :: FaceMap -> (FaceMap,Sign)
lastFace (FaceMap []) = error "lastFace"
lastFace (FaceMap [s]) = (FaceMap [], s)
lastFace (FaceMap (s:ss)) =
    let (FaceMap ss', l) = lastFace (FaceMap ss)
    in (FaceMap (s:ss'), l)

{-
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
-}
