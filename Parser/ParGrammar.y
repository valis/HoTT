-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Parser.ParGrammar where
import Parser.AbsGrammar
import Parser.LexGrammar
import Parser.ErrM

}

%name pDefs Defs

-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype { Token }

%token 
 ')' { PT _ (TS _ 1) }
 '*' { PT _ (TS _ 2) }
 '->' { PT _ (TS _ 3) }
 ':' { PT _ (TS _ 4) }
 ';' { PT _ (TS _ 5) }
 '=' { PT _ (TS _ 6) }
 'in' { PT _ (TS _ 7) }
 'let' { PT _ (TS _ 8) }
 '{' { PT _ (TS _ 9) }
 '}' { PT _ (TS _ 10) }

L_U { PT _ (T_U _) }
L_PLam { PT _ (T_PLam _) }
L_PPar { PT _ (T_PPar _) }
L_PInt { PT _ (T_PInt _) }
L_PIdp { PT _ (T_PIdp _) }
L_PR { PT _ (T_PR _) }
L_PSuc { PT _ (T_PSuc _) }
L_PNat { PT _ (T_PNat _) }
L_Pus { PT _ (T_Pus _) }
L_PTrans { PT _ (T_PTrans _) }
L_PIdent { PT _ (T_PIdent _) }
L_err    { _ }


%%

U    :: { U} : L_U { U (mkPosToken $1)}
PLam    :: { PLam} : L_PLam { PLam (mkPosToken $1)}
PPar    :: { PPar} : L_PPar { PPar (mkPosToken $1)}
PInt    :: { PInt} : L_PInt { PInt (mkPosToken $1)}
PIdp    :: { PIdp} : L_PIdp { PIdp (mkPosToken $1)}
PR    :: { PR} : L_PR { PR (mkPosToken $1)}
PSuc    :: { PSuc} : L_PSuc { PSuc (mkPosToken $1)}
PNat    :: { PNat} : L_PNat { PNat (mkPosToken $1)}
Pus    :: { Pus} : L_Pus { Pus (mkPosToken $1)}
PTrans    :: { PTrans} : L_PTrans { PTrans (mkPosToken $1)}
PIdent    :: { PIdent} : L_PIdent { PIdent (mkPosToken $1)}

Defs :: { Defs }
Defs : ListDef { Defs $1 } 


Def :: { Def }
Def : PIdent ListArg '=' Expr { Def $1 (reverse $2) $4 } 
  | PIdent ':' Expr { DefType $1 $3 }


ListDef :: { [Def] }
ListDef : {- empty -} { [] } 
  | Def { (:[]) $1 }
  | Def ';' ListDef { (:) $1 $3 }


Expr :: { Expr }
Expr : 'let' '{' ListDef '}' 'in' Expr { Let $3 $6 } 
  | PLam ListBinder '->' Expr { Lam $1 $2 $4 }
  | Expr1 { $1 }


Expr1 :: { Expr }
Expr1 : Expr3 '->' Expr1 { Arr $1 $3 } 
  | ListTypedVar '->' Expr1 { Pi $1 $3 }
  | Expr2 { $1 }


Expr2 :: { Expr }
Expr2 : Expr3 '*' Expr2 { Prod $1 $3 } 
  | ListTypedVar '*' Expr2 { Sigma $1 $3 }
  | Expr3 { $1 }


Expr3 :: { Expr }
Expr3 : Expr4 '=' Expr4 { Id $1 $3 } 
  | Expr4 { $1 }


Expr4 :: { Expr }
Expr4 : Expr4 Expr5 { App $1 $2 } 
  | Expr5 { $1 }


Expr5 :: { Expr }
Expr5 : Arg { Var $1 } 
  | PNat { Nat $1 }
  | PSuc { Suc $1 }
  | PR { Rec $1 }
  | PIdp { Idp $1 }
  | PTrans { Trans $1 }
  | PInt { NatConst $1 }
  | U { Universe $1 }
  | PPar Expr ')' { Paren $1 $2 }


Arg :: { Arg }
Arg : PIdent { Arg $1 } 
  | Pus { NoArg $1 }


ListArg :: { [Arg] }
ListArg : {- empty -} { [] } 
  | ListArg Arg { flip (:) $1 $2 }


Binder :: { Binder }
Binder : Arg { Binder $1 } 


ListBinder :: { [Binder] }
ListBinder : Binder { (:[]) $1 } 
  | Binder ListBinder { (:) $1 $2 }


TypedVar :: { TypedVar }
TypedVar : PPar Expr ':' Expr ')' { TypedVar $1 $2 $4 } 


ListTypedVar :: { [TypedVar] }
ListTypedVar : TypedVar { (:[]) $1 } 
  | TypedVar ListTypedVar { (:) $1 $2 }



{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
}
