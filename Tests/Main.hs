module Main
    ( main
    ) where

import qualified Data.Map as M
import Control.Monad
import System.Environment
import System.Directory
import Test.HUnit
import Data.List
import Text.PrettyPrint
import Control.DeepSeq
import Data.Maybe

import Parser.ErrM
import qualified Parser.AbsGrammar as R
import Parser.ParGrammar
import Parser.LayoutGrammar

import Syntax.Raw
import Syntax.Term
import Value
import ErrorDoc
import TypeChecking

processDecl :: String -> [R.Arg] -> R.Expr -> Maybe R.Expr -> TCM ([String],Term,Term,Ctx)
processDecl name args expr ty = do
    let p = if null args then getPos expr else argGetPos (head args)
    (_,ctx,ev,tv) <- evalDecl name (R.Lam (R.PLam (p,"\\")) (map R.Binder args) expr) ty
    let Def _ mty e' = simplifyDef $ Def name (Just (reifyType 0 tv, [])) (reify 0 ev tv)
        (ty,args) = fromMaybe (error "processDecl") mty
    return (args,e',ty,ctx)

processDecls :: Ctx -> [(String,Maybe R.Expr,[R.Arg],R.Expr)] -> [(String, EDocM Def)]
processDecls _ [] = []
processDecls ctx ((name,ty,args,expr) : decls) = case runTCM (processDecl name args expr ty) 0 [] M.empty ctx of
    Left errs -> (name, Left errs) : processDecls ctx decls
    Right (args',expr',ty',ctx') -> (name, Right (Def name (Just (ty',args')) expr')) : processDecls ctx' decls

parser :: String -> Err R.Defs
parser = pDefs . resolveLayout True . myLexer

testFile :: Bool -> String -> String -> Test
testFile onlyTC file cnt = TestLabel (takeWhile (/= '.') file) $ case parser cnt of
    Bad s -> TestCase (assertFailure s)
    Ok (R.Defs defs) -> case fmap (processDecls (M.empty,[]) . processDefs) (preprocessDefs defs) of
        Left errs -> TestCase $ assertFailure (errsToStr errs)
        Right res -> TestList $ flip map res $ \(name,edef) -> TestLabel name $ TestCase $ case edef of
            Left errs -> do
                assertBool (errsToStr errs) (isSuffixOf "fail" name)
                errsToStr errs `deepseq` return ()
            Right def -> do
                assertBool "" $ not (isSuffixOf "fail" name)
                when (not onlyTC) $ render (ppDef [] def) `deepseq` return ()
  where
    errsToStr = intercalate "\n\n" . map (erenderWithFilename file)

main = do
    args <- getArgs
    files <- getDirectoryContents "tests"
    let onlyTC = elem "-t" args
        files' = filter (not . isInfixOf "_output") files
    files' <- filterM (doesFileExist . ("tests/" ++)) files'
    cnts <- mapM (\file -> fmap (\cnt -> (file,cnt)) $ readFile $ "tests/" ++ file) files'
    runTestTT $ TestList $ map (\(file,cnt) -> testFile onlyTC file cnt) cnts
