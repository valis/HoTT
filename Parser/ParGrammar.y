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
 ',' { PT _ (TS _ 3) }
 '->' { PT _ (TS _ 4) }
 ':' { PT _ (TS _ 5) }
 '::' { PT _ (TS _ 6) }
 ';' { PT _ (TS _ 7) }
 '=' { PT _ (TS _ 8) }
 'in' { PT _ (TS _ 9) }
 'let' { PT _ (TS _ 10) }
 '{' { PT _ (TS _ 11) }
 '}' { PT _ (TS _ 12) }

L_U { PT _ (T_U _) }
L_PLam { PT _ (T_PLam _) }
L_PPar { PT _ (T_PPar _) }
L_PInt { PT _ (T_PInt _) }
L_PIdp { PT _ (T_PIdp _) }
L_PR { PT _ (T_PR _) }
L_PSuc { PT _ (T_PSuc _) }
L_PNat { PT _ (T_PNat _) }
L_Pus { PT _ (T_Pus _) }
L_PExt { PT _ (T_PExt _) }
L_Ppmap { PT _ (T_Ppmap _) }
L_PCoe { PT _ (T_PCoe _) }
L_PProjl { PT _ (T_PProjl _) }
L_PProjr { PT _ (T_PProjr _) }
L_PIso { PT _ (T_PIso _) }
L_PComp { PT _ (T_PComp _) }
L_PInv { PT _ (T_PInv _) }
L_PInvIdp { PT _ (T_PInvIdp _) }
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
PExt    :: { PExt} : L_PExt { PExt (mkPosToken $1)}
Ppmap    :: { Ppmap} : L_Ppmap { Ppmap (mkPosToken $1)}
PCoe    :: { PCoe} : L_PCoe { PCoe (mkPosToken $1)}
PProjl    :: { PProjl} : L_PProjl { PProjl (mkPosToken $1)}
PProjr    :: { PProjr} : L_PProjr { PProjr (mkPosToken $1)}
PIso    :: { PIso} : L_PIso { PIso (mkPosToken $1)}
PComp    :: { PComp} : L_PComp { PComp (mkPosToken $1)}
PInv    :: { PInv} : L_PInv { PInv (mkPosToken $1)}
PInvIdp    :: { PInvIdp} : L_PInvIdp { PInvIdp (mkPosToken $1)}
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
Expr1 : Expr2 '->' Expr1 { Arr $1 $3 } 
  | ListTypedVar '->' Expr1 { Pi $1 $3 }
  | Expr4 '::' Expr1 { Typed $1 $3 }
  | Expr2 { $1 }


Expr2 :: { Expr }
Expr2 : Expr3 '*' Expr2 { Prod $1 $3 } 
  | ListTypedVar '*' Expr2 { Sigma $1 $3 }
  | Expr3 { $1 }


Expr3 :: { Expr }
Expr3 : Expr4 '=' Expr4 { Id $1 $3 } 
  | Expr4 { $1 }


Expr4 :: { Expr }
Expr4 : Expr4 ',' Expr5 { Pair $1 $3 } 
  | Expr5 { $1 }


Expr5 :: { Expr }
Expr5 : Expr5 Expr6 { App $1 $2 } 
  | Expr6 { $1 }


Expr6 :: { Expr }
Expr6 : Arg { Var $1 } 
  | PNat { Nat $1 }
  | PSuc { Suc $1 }
  | PR { Rec $1 }
  | PIdp { Idp $1 }
  | PExt { Ext $1 }
  | Ppmap { Pmap $1 }
  | PCoe { Coe $1 }
  | PProjl { Proj1 $1 }
  | PProjr { Proj2 $1 }
  | PIso { Iso $1 }
  | PComp { Comp $1 }
  | PInv { Inv $1 }
  | PInvIdp { InvIdp $1 }
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

