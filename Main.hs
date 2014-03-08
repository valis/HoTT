module Main(main) where

import qualified Data.Map as M
import System.Environment
import System.IO
import Data.List
import Data.Either
import Control.Monad
import Control.Monad.State

import Parser.ErrM
import Parser.AbsGrammar
import Parser.ParGrammar
import Parser.LayoutGrammar
import Parser.PrintGrammar hiding (render)

import Eval
import ErrorDoc

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

processDecl :: String -> [Arg] -> Expr -> Maybe Expr -> StateT (Ctx,Ctx) (Either [EDoc]) ([String],Expr,Expr)
processDecl name args expr ty = do
    let p = if null args then getPos expr else argGetPos (head args)
    (ev,tv) <- evalDecl name (Lam (PLam (p,"\\")) (map Binder args) expr) ty
    (gctx,ctx) <- get
    let fv = (M.keys ctx ++ M.keys gctx)
        (a,e') = extractArgs $ unNorm (reify fv ev tv)
        t = unNorm $ reify fv tv (Stype maxBound)
    return (a,e',t)
  where
    extractArgs :: Expr -> ([String],Expr)
    extractArgs (Lam _ xs e) = let (ys,r) = extractArgs e in (map unBinder xs ++ ys, r)
    extractArgs e = ([],e)

processDecls :: Ctx -> [(String,Maybe Expr,[Arg],Expr)] -> [Either [EDoc] (String,Expr,[String],Expr)]
processDecls _ [] = []
processDecls ctx ((name,ty,args,expr) : decls) = case runStateT (processDecl name args expr ty) (ctx,M.empty) of
    Left errs -> Left errs : processDecls ctx decls
    Right ((args',expr',ty'),(ctx',_)) -> Right (name,ty',args',expr') : processDecls ctx' decls

run :: Err Defs -> (String,String)
run (Bad s) = (s,"")
run (Ok (Defs defs)) =
    let (errs,res) = either (\e -> ([e],[])) (partitionEithers . processDecls M.empty) (processDefs defs)
    in (intercalate "\n\n" (map render $ concat errs), intercalate "\n\n" (map print res))
  where
    print :: (String,Expr,[String],Expr) -> String
    print (x,t,[],e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " = " ++ printTree e
    print (x,t,as,e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " " ++ unwords as ++ " = " ++ printTree e

runFile :: String -> IO ()
runFile input = do
    cnt <- readFile input
    let (errs,res) = run (parser cnt)
    when (not $ null errs) (hPutStrLn stderr errs)
    when (not $ null res) $ writeFile (outputFilename input) (res ++ "\n")

main :: IO ()
main = getArgs >>= mapM_ runFile
