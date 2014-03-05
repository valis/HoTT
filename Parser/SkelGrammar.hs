module Parser.SkelGrammar where

-- Haskell module generated by the BNF converter

import Parser.AbsGrammar
import Parser.ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transU :: U -> Result
transU x = case x of
  U str  -> failure x


transPIdent :: PIdent -> Result
transPIdent x = case x of
  PIdent str  -> failure x


transDefs :: Defs -> Result
transDefs x = case x of
  Defs defs  -> failure x


transDef :: Def -> Result
transDef x = case x of
  Def pident args expr  -> failure x
  DefType pident expr  -> failure x


transExpr :: Expr -> Result
transExpr x = case x of
  Lam binders expr  -> failure x
  Arr expr1 expr2  -> failure x
  Pi typedvars expr  -> failure x
  Prod expr1 expr2  -> failure x
  Sigma typedvars expr  -> failure x
  Id expr1 expr2  -> failure x
  App expr1 expr2  -> failure x
  Var arg  -> failure x
  Nat  -> failure x
  Suc  -> failure x
  Rec  -> failure x
  NatConst n  -> failure x
  Universe u  -> failure x


transArg :: Arg -> Result
transArg x = case x of
  Arg pident  -> failure x
  NoArg  -> failure x


transBinder :: Binder -> Result
transBinder x = case x of
  Binder arg  -> failure x


transTypedVar :: TypedVar -> Result
transTypedVar x = case x of
  TypedVar expr1 expr2  -> failure x



