module Main(main) where

import qualified Data.Map as M
import System.Environment
import System.IO
import Data.List
import Data.Either
import Data.Maybe
import Control.Monad
import qualified Text.PrettyPrint as P

import Parser.ErrM
import qualified Parser.AbsGrammar as R
import Parser.ParGrammar
import Parser.LayoutGrammar

import Syntax.Raw
import Syntax.Term
import Value
import ErrorDoc
import TypeChecking
import TypeInference
import TCM
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
        (w,_:s') -> w : splitDots s'
    
    insert :: [String] -> String
    insert [] = ""
    insert [s] = s ++ "_output"
    insert [s1,s2] = s1 ++ "_output." ++ s2
    insert (x1:xs) = x1 ++ "." ++ insert xs

parser :: String -> Err R.Defs
parser = pDefs . resolveLayout True . myLexer

evalDecl :: String -> R.Expr -> Maybe R.Expr -> TCM (M.Map String DBIndex, Ctx, Value, Value)
evalDecl name expr mty = do
    ctx <- askCtx
    (er,tv) <- case mty of
        Nothing -> do
            er <- typeCheck expr Nothing
            tv <- typeOf er
            return (er,tv)
        Just ty -> do
            tr <- typeCheck ty Nothing
            let tv = eval 0 (ctxToCtxV ctx) tr
            er <- typeCheck expr (Just tv)
            return (er, tv)
    let ev = eval 0 (ctxToCtxV ctx) er
    (_, _, mctx, (gctx, lctx)) <- ask
    return (M.delete name mctx, (M.insert name (ev,tv) gctx, lctx), ev, tv)

processDecl :: String -> [R.Arg] -> R.Expr -> Maybe R.Expr -> TCM ([String],Term,Term,Ctx)
processDecl name args expr ty = do
    let p = if null args then getPos expr else argGetPos (head args)
    (_,ctx,ev,tv) <- evalDecl name (R.Lam (R.PLam (p,"\\")) (map R.Binder args) expr) ty
    let Def _ mty e' = simplifyDef $ Def name (Just (reifyType 0 0 tv, [])) (reify 0 0 ev tv)
        (ty,args) = fromMaybe (error "processDecl") mty
    return (args,e',ty,ctx)

processDecls :: Ctx -> [(String,Maybe R.Expr,[R.Arg],R.Expr)] -> [EDocM Def]
processDecls _ [] = []
processDecls ctx ((name,ty,args,expr) : decls) = case runTCM (processDecl name args expr ty) 0 [] M.empty ctx of
    Left errs -> Left errs : processDecls ctx decls
    Right (args',expr',ty',ctx') -> Right (Def name (Just (ty',args')) expr') : processDecls ctx' decls

run :: String -> Err R.Defs -> (String,String)
run _ (Bad s) = (s,"")
run fn (Ok (R.Defs defs)) =
    let (errs,res) = either (\e -> ([e],[])) (partitionEithers . processDecls (M.empty,[]))
            $ fmap processDefs (preprocessDefs defs)
    in (intercalate "\n\n" $ map (erenderWithFilename fn) (concat errs), intercalate "\n\n" $ map (P.render . ppDef []) res)

runFile :: Bool -> String -> IO ()
runFile b input = do
    cnt <- readFile input
    let (errs,res) = run input (parser cnt)
    when (not $ null errs) (hPutStrLn stderr errs)
    when (b && not (null res)) $ writeFile (outputFilename input) (res ++ "\n")

main :: IO ()
main = do
    args <- getArgs
    if elem "-t" args
        then mapM_ (runFile False) (delete "-t" args)
        else mapM_ (runFile True) args
