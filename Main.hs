module Main(main) where

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

processDefs :: [Def] -> [Either String (String,Expr,[String],Expr)]
processDefs = undefined

run :: Err Defs -> (String,String)
run (Bad s) = (s,"")
run (Ok (Defs defs)) =
    let (errs,res) = partitionEithers (processDefs defs)
    in (concat errs, intercalate "\n\n" $ map print res)
  where
    print :: (String,Expr,[String],Expr) -> String
    print (x,t,as,e) = x ++ " : " ++ printTree t ++ "\n" ++ x ++ " " ++ unwords as ++ " = " ++ printTree e

runFile :: String -> IO ()
runFile input = do
    cnt <- readFile input
    let (errs,res) = run (parser cnt)
    when (not $ null errs) (hPutStrLn stderr errs)
    when (not $ null res) $ writeFile (outputFilename input) res

main :: IO ()
main = getArgs >>= mapM_ runFile
