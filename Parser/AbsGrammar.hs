module Parser.AbsGrammar where

-- Haskell module generated by the BNF converter


newtype U = U ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PLam = PLam ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PPar = PPar ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PInt = PInt ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PIdp = PIdp ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PR = PR ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PSuc = PSuc ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PNat = PNat ((Int,Int),String) deriving (Eq,Ord,Show)
newtype Pus = Pus ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PExt = PExt ((Int,Int),String) deriving (Eq,Ord,Show)
newtype Ppmap = Ppmap ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PTrans = PTrans ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PIdent = PIdent ((Int,Int),String) deriving (Eq,Ord,Show)
data Defs =
   Defs [Def]
  deriving (Eq,Ord,Show)

data Def =
   Def PIdent [Arg] Expr
 | DefType PIdent Expr
  deriving (Eq,Ord,Show)

data Expr =
   Let [Def] Expr
 | Lam PLam [Binder] Expr
 | Arr Expr Expr
 | Pi [TypedVar] Expr
 | Prod Expr Expr
 | Sigma [TypedVar] Expr
 | Id Expr Expr
 | App Expr Expr
 | Var Arg
 | Nat PNat
 | Suc PSuc
 | Rec PR
 | Idp PIdp
 | Ext PExt Expr Expr
 | Pmap Ppmap
 | Trans PTrans
 | NatConst PInt
 | Universe U
 | Paren PPar Expr
  deriving (Eq,Ord,Show)

data Arg =
   Arg PIdent
 | NoArg Pus
  deriving (Eq,Ord,Show)

data Binder =
   Binder Arg
  deriving (Eq,Ord,Show)

data TypedVar =
   TypedVar PPar Expr Expr
  deriving (Eq,Ord,Show)

