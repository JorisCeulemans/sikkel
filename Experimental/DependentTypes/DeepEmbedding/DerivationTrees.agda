module Experimental.DependentTypes.DeepEmbedding.DerivationTrees where

open import Data.Nat

open import Experimental.DependentTypes.DeepEmbedding.Syntax.ForDerivations

private variable
  Γ Δ Θ : CtxExpr
  T S A : TyExpr
  t s f b p : TmExpr
  τ σ : SubstExpr


infix 3 _⊢var_∈_
data _⊢var_∈_ : CtxExpr → ℕ → TyExpr → Set where
  var-zero : Γ ,, A ⊢var 0 ∈ A [ π ]
  var-suc : ∀ {x} → Γ ⊢var x ∈ T → Γ ,, A ⊢var suc x ∈ T [ π ]

infix 3 _⊢ctx _⊢_⇒_ _⊢ty_ _⊢_∈_
data _⊢ctx : CtxExpr → Set
data _⊢_⇒_ : CtxExpr → SubstExpr → CtxExpr → Set
data _⊢ty_ : CtxExpr → TyExpr → Set
data _⊢_∈_ : CtxExpr → TmExpr → TyExpr → Set

data _⊢ctx where
  d-◇ : ◇ ⊢ctx
  d-,, : Γ ⊢ctx → Γ ⊢ty T → Γ ,, T ⊢ctx

data _⊢_⇒_ where
  d-id-subst : Γ ⊢ctx → Γ ⊢ id-subst ⇒ Γ
  d-⊚ : (Γ ⊢ τ ⇒ Θ) → (Δ ⊢ σ ⇒ Γ) → (Δ ⊢ τ ⊚ σ ⇒ Θ)
  d-π : Γ ⊢ty T → Γ ,, T ⊢ π ⇒ Γ

data _⊢ty_ where
  d-Nat : Γ ⊢ctx → Γ ⊢ty Nat
  d-Bool : Γ ⊢ctx → Γ ⊢ty Bool
  d-⇛ : Γ ⊢ty T → Γ ⊢ty S → Γ ⊢ty T ⇛ S
  d-⊠ : Γ ⊢ty T → Γ ⊢ty S → Γ ⊢ty T ⊠ S
  d-Id : Γ ⊢ t ∈ T → Γ ⊢ s ∈ T → Γ ⊢ty Id t s
  d-ty-subst : Γ ⊢ty T → Δ ⊢ σ ⇒ Γ → Δ ⊢ty T [ σ ]

data _⊢_∈_ where
  d-var : ∀ {x} → Γ ⊢var x ∈ T → Γ ⊢ var x ∈ T
  d-lam : Γ ,, A ⊢ t ∈ T [ π ] → Γ ⊢ lam A t ∈ A ⇛ T
  d-app : Γ ⊢ f ∈ T ⇛ S → Γ ⊢ t ∈ T → Γ ⊢ f ∙ t ∈ S
  d-lit : ∀ {n} → Γ ⊢ctx → Γ ⊢ lit n ∈ Nat
  d-suc : Γ ⊢ctx → Γ ⊢ suc ∈ Nat ⇛ Nat
  d-plus : Γ ⊢ctx → Γ ⊢ plus ∈ Nat ⇛ Nat ⇛ Nat
  d-true : Γ ⊢ctx → Γ ⊢ true ∈ Bool
  d-false : Γ ⊢ctx → Γ ⊢ false ∈ Bool
  d-if : Γ ⊢ b ∈ Bool → Γ ⊢ t ∈ T → Γ ⊢ f ∈ T → Γ ⊢ if b t f ∈ T
  d-pair : Γ ⊢ t ∈ T → Γ ⊢ s ∈ S → Γ ⊢ pair t s ∈ T ⊠ S
  d-fst : Γ ⊢ p ∈ T ⊠ S → Γ ⊢ fst p ∈ T
  d-snd : Γ ⊢ p ∈ T ⊠ S → Γ ⊢ snd p ∈ S
  d-refl : Γ ⊢ t ∈ T → Γ ⊢ refl t ∈ Id t t
  d-tm-subst : Γ ⊢ t ∈ T → Δ ⊢ σ ⇒ Γ → Δ ⊢ t [ σ ] ∈ T [ σ ]
