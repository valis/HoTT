module Main(main) where

import System.Environment

import Parser.ErrM
import Parser.AbsGrammar
import Parser.ParGrammar
import Parser.LayoutGrammar

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

processDef :: Def -> String
processDef = undefined

run :: Err Defs -> Either String String
run (Bad s) = Left s
run (Ok (Defs defs)) = Right (concatMap processDef defs)

runFile :: String -> IO ()
runFile input = readFile input >>= either putStrLn (writeFile output) . run . parser
  where output = outputFilename input

main :: IO ()
main = getArgs >>= mapM_ runFile
