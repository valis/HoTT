module ErrorDoc
    ( EMsg, EDoc, EDocM
    , EPretty(..)
    , etext, enull, (<>), (<+>), ($$)
    , emsg, emsgL, emsgLC
    , eprettyLevel, eprettyHead
    , erender, erenderWithFilename
    , liftErr2
    ) where

import qualified Text.PrettyPrint as P

import Syntax.Term

data EMsg = EMsg (Maybe Int) (Maybe Int) String EDoc
data EDoc = EText String | ENull | ETerm (Maybe Int) Term | EAbove EDoc EDoc | EBeside EDoc Bool EDoc

class EPretty a where
    epretty :: a -> EDoc

instance EPretty Term where
    epretty = ETerm Nothing

type EDocM = Either [EMsg]

liftErr2 :: (a -> b -> EDocM c) -> EDocM a -> EDocM b -> EDocM c
liftErr2 f (Left m1) (Left m2) = Left (m1 ++ m2)
liftErr2 f (Left m) _ = Left m
liftErr2 f _ (Left m) = Left m
liftErr2 f (Right v1) (Right v2) = f v1 v2

eprettyLevel :: Int -> Term -> EDoc
eprettyLevel n e | n < 0 = epretty e
                 | otherwise = ETerm (Just n) e

eprettyHead :: Term -> EDoc
eprettyHead = eprettyLevel 1

etext :: String -> EDoc
etext = EText

enull :: EDoc
enull = ENull

infixl 6 <>, <+>
infixl 5 $$
(<>) :: EDoc -> EDoc -> EDoc
d1 <> d2 = EBeside d1 False d2

(<+>) :: EDoc -> EDoc -> EDoc
d1 <+> d2 = EBeside d1 True d2

($$) :: EDoc -> EDoc -> EDoc
($$) = EAbove

emsg :: String -> EDoc -> EMsg
emsg = EMsg Nothing Nothing

emsgL :: Int -> String -> EDoc -> EMsg
emsgL l = EMsg (Just l) Nothing

emsgLC :: Int -> Int -> String -> EDoc -> EMsg
emsgLC l c = EMsg (Just l) (Just c)

erender :: EMsg -> String
erender (EMsg l c s d) = P.render (msgToDoc Nothing l c s d)

erenderWithFilename :: String -> EMsg -> String
erenderWithFilename fn (EMsg l c s d) = P.render (msgToDoc (Just fn) l c s d)

msgToDoc :: Maybe String -> Maybe Int -> Maybe Int -> String -> EDoc -> P.Doc
msgToDoc fn l c s d = P.hang (edocToDoc $
    maybe enull (\s -> etext $ s ++ ":") fn <>
    maybe enull (\ln -> etext $ show ln ++ ":") l <>
    maybe enull (\cn -> etext $ show cn ++ ":") c <+> etext s) 4 (edocToDoc d)

edocToDoc :: EDoc -> P.Doc
edocToDoc ENull = P.empty
edocToDoc (EText "") = P.empty
edocToDoc (EText s) = P.text s
edocToDoc (EBeside d1 False d2) = edocToDoc d1 P.<> edocToDoc d2
edocToDoc (EBeside d1 True d2) = edocToDoc d1 P.<+> edocToDoc d2
edocToDoc (EAbove d1 d2) = edocToDoc d1 P.$+$ edocToDoc d2
edocToDoc (ETerm l e) = ppTerm l e
