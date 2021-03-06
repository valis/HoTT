{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Parser.PrintGrammar where

-- pretty-printer generated by the BNF converter

import Parser.AbsGrammar
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)



instance Print U where
  prt _ (U (_,i)) = doc (showString ( i))


instance Print PLam where
  prt _ (PLam (_,i)) = doc (showString ( i))


instance Print PPar where
  prt _ (PPar (_,i)) = doc (showString ( i))


instance Print PInt where
  prt _ (PInt (_,i)) = doc (showString ( i))


instance Print PIdp where
  prt _ (PIdp (_,i)) = doc (showString ( i))


instance Print PR where
  prt _ (PR (_,i)) = doc (showString ( i))


instance Print PSuc where
  prt _ (PSuc (_,i)) = doc (showString ( i))


instance Print PNat where
  prt _ (PNat (_,i)) = doc (showString ( i))


instance Print Pus where
  prt _ (Pus (_,i)) = doc (showString ( i))


instance Print PCoe where
  prt _ (PCoe (_,i)) = doc (showString ( i))


instance Print Ppcon where
  prt _ (Ppcon (_,i)) = doc (showString ( i))


instance Print PProjl where
  prt _ (PProjl (_,i)) = doc (showString ( i))


instance Print PProjr where
  prt _ (PProjr (_,i)) = doc (showString ( i))


instance Print PIso where
  prt _ (PIso (_,i)) = doc (showString ( i))


instance Print PIdent where
  prt _ (PIdent (_,i)) = doc (showString ( i))



instance Print Defs where
  prt i e = case e of
   Defs defs -> prPrec i 0 (concatD [prt 0 defs])


instance Print Def where
  prt i e = case e of
   Def pident args expr -> prPrec i 0 (concatD [prt 0 pident , prt 0 args , doc (showString "=") , prt 0 expr])
   DefType pident expr -> prPrec i 0 (concatD [prt 0 pident , doc (showString ":") , prt 0 expr])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Expr where
  prt i e = case e of
   Let defs expr -> prPrec i 0 (concatD [doc (showString "let") , doc (showString "{") , prt 0 defs , doc (showString "}") , doc (showString "in") , prt 0 expr])
   Lam plam binders expr -> prPrec i 0 (concatD [prt 0 plam , prt 0 binders , doc (showString "->") , prt 0 expr])
   Arr expr0 expr -> prPrec i 1 (concatD [prt 2 expr0 , doc (showString "->") , prt 1 expr])
   Pi typedvars expr -> prPrec i 1 (concatD [prt 0 typedvars , doc (showString "->") , prt 1 expr])
   Prod expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString "*") , prt 2 expr])
   Sigma typedvars expr -> prPrec i 2 (concatD [prt 0 typedvars , doc (showString "*") , prt 2 expr])
   Over expr0 expr -> prPrec i 3 (concatD [prt 4 expr0 , doc (showString "|") , prt 3 expr])
   Id expr0 expr -> prPrec i 4 (concatD [prt 5 expr0 , doc (showString "=") , prt 5 expr])
   Pair expr0 expr -> prPrec i 5 (concatD [prt 5 expr0 , doc (showString ",") , prt 6 expr])
   Pmap expr0 expr -> prPrec i 6 (concatD [prt 6 expr0 , doc (showString "<*>") , prt 7 expr])
   App expr0 expr -> prPrec i 7 (concatD [prt 7 expr0 , prt 8 expr])
   Var arg -> prPrec i 8 (concatD [prt 0 arg])
   Nat pnat -> prPrec i 8 (concatD [prt 0 pnat])
   Suc psuc -> prPrec i 8 (concatD [prt 0 psuc])
   Rec pr -> prPrec i 8 (concatD [prt 0 pr])
   Idp pidp -> prPrec i 8 (concatD [prt 0 pidp])
   Coe pcoe -> prPrec i 8 (concatD [prt 0 pcoe])
   Proj1 pprojl -> prPrec i 8 (concatD [prt 0 pprojl])
   Proj2 pprojr -> prPrec i 8 (concatD [prt 0 pprojr])
   Pcon ppcon -> prPrec i 8 (concatD [prt 0 ppcon])
   Iso piso -> prPrec i 8 (concatD [prt 0 piso])
   NatConst pint -> prPrec i 8 (concatD [prt 0 pint])
   Universe u -> prPrec i 8 (concatD [prt 0 u])
   Paren ppar expr -> prPrec i 8 (concatD [prt 0 ppar , prt 0 expr , doc (showString ")")])


instance Print Arg where
  prt i e = case e of
   Arg pident -> prPrec i 0 (concatD [prt 0 pident])
   NoArg pus -> prPrec i 0 (concatD [prt 0 pus])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Binder where
  prt i e = case e of
   Binder arg -> prPrec i 0 (concatD [prt 0 arg])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print TypedVar where
  prt i e = case e of
   TypedVar ppar expr0 expr -> prPrec i 0 (concatD [prt 0 ppar , prt 0 expr0 , doc (showString ":") , prt 0 expr , doc (showString ")")])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , prt 0 xs])


