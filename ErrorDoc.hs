module ErrorDoc
    ( Pretty(..)
    , textL, textLC, msgL, msgLC, docL, docLC
    , module Text.PrettyPrint
    , prettyLevel
    , prettyHead
    ) where

import Text.PrettyPrint

import Parser.AbsGrammar
import Parser.PrintGrammar(printTree)

class Pretty a where
    pretty :: a -> Doc

instance Pretty Expr where
    pretty = text . printTree

prettyLevel :: Int -> Expr -> Doc
prettyLevel n e | n < 0 = pretty e
prettyLevel 0 _ = text "_"
prettyLevel _ e = pretty e -- TODO: Define it

prettyHead :: Expr -> Doc
prettyHead = prettyLevel 1

textL :: Int -> String -> Doc
textL l s = text (show l ++ ":") <+> text s

textLC :: Int -> Int -> String -> Doc
textLC l c s = text (show l ++ ":" ++ show c ++ ":") <+> text s

msgL :: Int -> String -> Doc -> Doc
msgL l s d = text (show l ++ ":") <+> text s $$ d

msgLC :: Int -> Int -> String -> Doc -> Doc
msgLC l c s d = text (show l ++ ":" ++ show c ++ ":") <+> text s $$ d

docL :: Int -> Doc -> Doc
docL l d = text (show l ++ ":") <+> d

docLC :: Int -> Int -> Doc -> Doc
docLC l c d = text (show l ++ ":" ++ show c ++ ":") <+> d
