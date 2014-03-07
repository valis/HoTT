module Main(main) where

import qualified Data.Map as M
import System.Environment
import System.IO
import Data.List
import Data.Either
import Control.Monad

import Parser.ErrM
import Parser.AbsGrammar
import Parser.ParGrammar
import Parser.LayoutGrammar
import Parser.PrintGrammar

import Eval

outputFilename :: String -> String
outputFilename input = case break (== '/') input of
    (l,[]) -> insert (splitDots l)
    (l,r)  -> l ++ "/" ++ outputFilename (tail r)
  where
    splitDots :: String -> [String]
    splitDots s = case break (== '.') s of
        ("",[]) -> []
        (w,[]) -> [w]
        (w,'.':s') -> w : splitDots s'
    
    insert :: [String] -> String
    insert [s] = s ++ "_output"
    insert [s1,s2] = s1 ++ "_output." ++ s2
    insert (x1:xs) = x1 ++ "." ++ insert xs

parser :: String -> Err Defs
parser = pDefs . resolveLayout True . myLexer

processExpr :: Ctx -> String -> Expr -> Maybe Expr -> Either [String] (Ctx,Expr,Expr)
processExpr ctx name expr mty = do
    tv <- case mty of
        Nothing -> typeOf ctx M.empty expr
        Just ty -> do
            typeOf ctx M.empty ty
            let tv = eval ctx ty 0 M.empty
            hasType ctx M.empty expr tv
            return tv
    let ev = evalOfType ctx expr tv 0 M.empty
    return (M.insert name (ev,tv) ctx, unNorm $ reify (M.keys ctx) ev tv, unNorm $ reify (M.keys ctx) tv $ Stype maxBound)

processDecl :: Ctx -> String -> [Arg] -> Expr -> Maybe Expr -> Either [String] (Ctx,[String],Expr,Expr)
processDecl ctx name args expr ty = do
    (ctx',e,t) <- processExpr ctx name (Lam (map Binder args) expr) ty
    let (a,e') = extractArgs e
    return (ctx',a,e',t)
  where
    extractArgs :: Expr -> ([String],Expr)
    extractArgs (Lam xs e) = let (ys,r) = extractArgs e in (map unBinder xs ++ ys, r)
    extractArgs e = ([],e)

processDefs :: [Def] -> [Either [String] (String,Expr,[String],Expr)]
processDefs defs =
    let typeSigsDup = duplicates (map fst typeSigs)
        funDeclsDup = duplicates (map fst funDecls)
    in if not (null typeSigsDup) || not (null funDeclsDup)
        then map (\name -> Left ["Duplicate type signatures for " ++ name]) typeSigsDup ++
             map (\name -> Left ["Multiple declarations of " ++ name]) funDeclsDup
        else processDecls M.empty funDecls
  where
    typeSigs = filterTypeSigs defs
    funDecls = filterFunDecls defs
    
    processDecls :: Ctx -> [(String,([Arg],Expr))] -> [Either [String] (String,Expr,[String],Expr)]
    processDecls _ [] = []
    processDecls ctx ((name,(args,expr)):decls) = case processDecl ctx name args expr (lookup name typeSigs) of
        Left errs -> Left errs : processDecls ctx decls
        Right (ctx',args',expr',ty) -> Right (name,ty,args',expr') : processDecls ctx' decls
    
    filterTypeSigs :: [Def] -> [(String,Expr)]
    filterTypeSigs [] = []
    filterTypeSigs (DefType (PIdent (_,x)) e : defs) = (x,e) : filterTypeSigs defs
    filterTypeSigs (_:defs) = filterTypeSigs defs
    
    filterFunDecls :: [Def] -> [(String,([Arg],Expr))]
    filterFunDecls [] = []
    filterFunDecls (Def (PIdent (_,x)) a e : defs) = (x,(a,e)) : filterFunDecls defs
    filterFunDecls (_:defs) = filterFunDecls defs
    
    duplicates :: [String] -> [String]
    duplicates [] = []
    duplicates (x:xs) = case findRemove xs of
        Nothing -> duplicates xs
        Just xs' -> x : duplicates xs'
      where
        findRemove :: [String] -> Maybe [String]
        findRemove [] = Nothing
        findRemove (y:ys) | x == y = Just $ maybe ys id (findRemove ys)
                          | otherwise = fmap (y:) (findRemove ys)

run :: Err Defs -> (String,String)
run (Bad s) = (s,"")
run (Ok (Defs defs)) =
    let (errs,res) = partitionEithers (processDefs defs)
    in (unlines (concat errs), intercalate "\n\n" (map print res) ++ "\n")
  where
    print :: (String,Expr,[String],Expr) -> String
    print (x,t,[],e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " = " ++ printTree e
    print (x,t,as,e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " " ++ unwords as ++ " = " ++ printTree e

runFile :: String -> IO ()
runFile input = do
    cnt <- readFile input
    let (errs,res) = run (parser cnt)
    when (not $ null errs) (hPutStr stderr errs)
    when (not $ null res) $ writeFile (outputFilename input) res

main :: IO ()
main = getArgs >>= mapM_ runFile
