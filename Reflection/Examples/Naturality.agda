--------------------------------------------------
-- Some tests for the naturality solver
--------------------------------------------------

open import Categories

module Reflection.Examples.Naturality {C : Category} where

open import Data.Bool
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Instances
open import Reflection.Naturality.Solver
open import Reflection.Tactic.Naturality

private
  variable
    Γ Δ Θ : Ctx C


example : (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
          ((Bool' ⇛ Bool') ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
example σ τ = type-naturality-reflect (sub (bin _⊠_ (bin _⇛_ (nul Bool') (nul Bool')) (sub (nul Bool') τ)) σ)
                                      (bin _⊠_ (sub (bin _⇛_ (nul Bool') (nul Bool')) σ) (nul Bool'))
                                      refl
                                      refl

example' : (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
           ((Bool' ⇛ Bool') ⊠ ((Discr Bool) [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
example' σ τ = by-naturality

-- Experiments interaction var + by-naturality tactics

not' : Tm Γ Bool' → Tm Γ Bool'
term (not' b) x _ = not (b ⟨ x , _ ⟩')
naturality (not' b) f eγ = cong not (naturality b f eγ)

not-fun : Tm {C = C} ◇ (Bool' ⇛ Bool')
not-fun = lam[ "b" ∈ Bool' ] ι[ by-naturality ] not' (ι[ by-naturality ] var "b")
