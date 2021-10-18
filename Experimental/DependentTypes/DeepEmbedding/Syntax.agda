module Experimental.DependentTypes.DeepEmbedding.Syntax where

open import Data.Nat

data TyExpr : Set
data TmExpr : Set

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr where
  Nat Bool : TyExpr
  _⇛_ _⊠_ : TyExpr → TyExpr → TyExpr
  Id : TmExpr → TmExpr → TyExpr

infixl 50 _∙_
data TmExpr where
  ann_∈_ : TmExpr → TyExpr → TmExpr
  var : ℕ → TmExpr
  lam : TyExpr → TmExpr → TmExpr
  _∙_ : TmExpr → TmExpr → TmExpr
  lit : ℕ → TmExpr
  suc plus : TmExpr
  true false : TmExpr
  if : TmExpr → TmExpr → TmExpr → TmExpr
  pair : TmExpr → TmExpr → TmExpr
  fst snd : TmExpr → TmExpr
  refl : TmExpr → TmExpr

infixl 4 _,,_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_ : (Γ : CtxExpr) → (T : TyExpr) → CtxExpr
