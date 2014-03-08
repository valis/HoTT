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


transPLam :: PLam -> Result
transPLam x = case x of
  PLam str  -> failure x


transPPar :: PPar -> Result
transPPar x = case x of
  PPar str  -> failure x


transPInt :: PInt -> Result
transPInt x = case x of
  PInt str  -> failure x


transPpmap :: Ppmap -> Result
transPpmap x = case x of
  Ppmap str  -> failure x


transPIdp :: PIdp -> Result
transPIdp x = case x of
  PIdp str  -> failure x


transPR :: PR -> Result
transPR x = case x of
  PR str  -> failure x


transPSuc :: PSuc -> Result
transPSuc x = case x of
  PSuc str  -> failure x


transPNat :: PNat -> Result
transPNat x = case x of
  PNat str  -> failure x


transPus :: Pus -> Result
transPus x = case x of
  Pus str  -> failure x


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
  Let defs expr  -> failure x
  Lam plam binders expr  -> failure x
  Arr expr1 expr2  -> failure x
  Pi typedvars expr  -> failure x
  Prod expr1 expr2  -> failure x
  Sigma typedvars expr  -> failure x
  Id expr1 expr2  -> failure x
  App expr1 expr2  -> failure x
  Var arg  -> failure x
  Nat pnat  -> failure x
  Suc psuc  -> failure x
  Rec pr  -> failure x
  Idp pidp  -> failure x
  Pmap ppmap expr  -> failure x
  NatConst pint  -> failure x
  Universe u  -> failure x
  Paren ppar expr  -> failure x


transArg :: Arg -> Result
transArg x = case x of
  Arg pident  -> failure x
  NoArg pus  -> failure x


transBinder :: Binder -> Result
transBinder x = case x of
  Binder arg  -> failure x


transTypedVar :: TypedVar -> Result
transTypedVar x = case x of
  TypedVar ppar expr1 expr2  -> failure x



