module ErrorDoc
    ( EDoc
    , EPretty(..)
    , etext, enull, (<>), (<+>), ($$)
    , etextL, etextLC, emsgL, emsgLC, edocL, edocLC
    , render
    ) where

import qualified Text.PrettyPrint as P

import Parser.AbsGrammar

data EDoc = EText String | EBeside EDoc Bool EDoc | EAbove EDoc EDoc | ENull

class EPretty a where
    epretty :: a -> EDoc

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

etextL :: Int -> String -> EDoc
etextL l s = etext (show l ++ ":") <+> etext s

etextLC :: Int -> Int -> String -> EDoc
etextLC l c s = etext (show l ++ ":" ++ show c ++ ":") <+> etext s

emsgL :: Int -> String -> EDoc -> EDoc
emsgL l s d = etext (show l ++ ":") <+> etext s $$ d

emsgLC :: Int -> Int -> String -> EDoc -> EDoc
emsgLC l c s d = etext (show l ++ ":" ++ show c ++ ":") <+> etext s $$ d

edocL :: Int -> EDoc -> EDoc
edocL l d = etext (show l ++ ":") <+> d

edocLC :: Int -> Int -> EDoc -> EDoc
edocLC l c d = etext (show l ++ ":" ++ show c ++ ":") <+> d

render :: EDoc -> String
render = P.render . edocToDoc
  where
    edocToDoc :: EDoc -> P.Doc
    edocToDoc ENull = P.empty
    edocToDoc (EText s) = P.text s
    edocToDoc (EBeside d1 False d2) = edocToDoc d1 P.<> edocToDoc d2
    edocToDoc (EBeside d1 True d2) = edocToDoc d1 P.<+> edocToDoc d2
    edocToDoc (EAbove d1 d2) = edocToDoc d1 P.$$ edocToDoc d2
