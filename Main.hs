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
    splitDots s = let (w,'.':s') = break (== '.') s in w : splitDots s'
    
    insert :: [String] -> String
    insert [s] = s ++ "_output"
    insert [s1,s2] = s1 ++ "_output." ++ s2
    insert (x1:xs) = x1 ++ "." ++ insert xs

parser :: String -> Err Defs
parser = pDefs . resolveLayout True . myLexer

processExpr :: String -> Expr -> Maybe Value -> Either [String] (Expr,Expr)
processExpr name expr mtv = do
    tv <- maybe (typeOf M.empty expr) (\tv -> hasType M.empty expr tv >> return tv) mtv
    let ev = evalOfType expr tv 0 M.empty
    return (unNorm $ reify [] ev tv, unNorm $ reify [] tv $ Stype maxBound)

processDecl :: String -> [Arg] -> Expr -> Maybe Value -> Either [String] ([String],Expr,Expr)
processDecl name args expr ty = do
    (e,t) <- processExpr name (Lam (map Binder args) expr) ty
    let (a,e') = extractArgs e
    return (a,e',t)
  where
    extractArgs :: Expr -> ([String],Expr)
    extractArgs (Lam xs e) = (map unBinder xs,e)
    extractArgs e = ([],e)

processDefs :: [Def] -> [Either [String] (String,Expr,[String],Expr)]
processDefs defs =
    let typeSigs = filterTypeSigs defs
        funDecls = filterFunDecls defs
        typeSigsDup = duplicates (map fst typeSigs)
        funDeclsDup = duplicates (map fst funDecls)
    in if not (null typeSigsDup) || not (null funDeclsDup)
        then map (\name -> Left ["Duplicate type signatures for " ++ name]) typeSigsDup ++
             map (\name -> Left ["Multiple declarations of " ++ name]) funDeclsDup
        else flip map funDecls $ \(name,(args,expr)) -> case lookup name typeSigs of
            Nothing -> fmap (\(a,e,t) -> (name,t,a,e)) (processDecl name args expr Nothing)
            Just ty -> do
                v <- typeOf M.empty ty
                (a,e,t) <- processDecl name args expr (Just v)
                return (name,t,a,e)
  where
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
    in (unlines (concat errs), intercalate "\n\n" $ map print res)
  where
    print :: (String,Expr,[String],Expr) -> String
    print (x,t,[],e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " = " ++ printTree e
    print (x,t,as,e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " " ++ unwords as ++ " = " ++ printTree e

runFile :: String -> IO ()
runFile input = do
    cnt <- readFile input
    let (errs,res) = run (parser cnt)
    when (not $ null errs) (hPutStrLn stderr errs)
    when (not $ null res) $ writeFile (outputFilename input) res

main :: IO ()
main = getArgs >>= mapM_ runFile
