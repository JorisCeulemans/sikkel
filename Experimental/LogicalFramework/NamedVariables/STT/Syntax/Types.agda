module Experimental.LogicalFramework.NamedVariables.STT.Syntax.Types where

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr : Set where
  Nat' : TyExpr
  Bool' : TyExpr
  _⇛_ : TyExpr → TyExpr → TyExpr
  _⊠_ : TyExpr → TyExpr → TyExpr
