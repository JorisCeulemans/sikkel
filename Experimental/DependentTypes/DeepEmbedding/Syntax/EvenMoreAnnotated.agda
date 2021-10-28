module Experimental.DependentTypes.DeepEmbedding.Syntax.EvenMoreAnnotated where

open import Data.Nat

open import MSTT.TCMonad


data TyExpr : Set
data TmExpr : Set

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr where
  Nat Bool : TyExpr
  _⇛_ _⊠_ : TyExpr → TyExpr → TyExpr
  Id : TyExpr → TmExpr → TmExpr → TyExpr

-- infixl 50 _∙_
data TmExpr where
  ann_∈_ : TmExpr → TyExpr → TmExpr
  var : ℕ → TmExpr
  lam : TyExpr → TmExpr → TmExpr
  app : TyExpr → TmExpr → TmExpr → TmExpr
  lit : ℕ → TmExpr
  suc plus : TmExpr
  true false : TmExpr
  if : TmExpr → TmExpr → TmExpr → TmExpr
  pair : TmExpr → TmExpr → TmExpr
  fst snd : TyExpr → TmExpr → TmExpr
  refl : TyExpr → TmExpr → TmExpr

infixl 4 _,,_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_ : (Γ : CtxExpr) → (T : TyExpr) → CtxExpr


data IsFunTy : TyExpr → Set where
  fun-ty : (T S : TyExpr) → IsFunTy (T ⇛ S)

is-fun-ty : (T : TyExpr) → TCM (IsFunTy T)
is-fun-ty (T ⇛ S) = ok (fun-ty T S)
is-fun-ty T = type-error ""

data IsProdTy : TyExpr → Set where
  prod-ty : (T S : TyExpr) → IsProdTy (T ⊠ S)

is-prod-ty : (T : TyExpr) → TCM (IsProdTy T)
is-prod-ty (T ⊠ S) = ok (prod-ty T S)
is-prod-ty T = type-error ""
