--------------------------------------------------
-- Some tests for the naturality solver
--------------------------------------------------

open import Categories

module Reflection.Examples.Naturality {C : Category} where

open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Reflection.Naturality
open import Reflection.Naturality.Instances
open import Reflection.Tactic.Naturality

example : {Δ : Ctx C} {Γ : Ctx C} {Θ : Ctx C} →
          (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
          ((Bool' ⇛ Bool') ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
example σ τ = type-naturality-reflect (sub (bin _⊠_ (bin _⇛_ (nul Bool') (nul Bool')) (sub (nul Bool') τ)) σ)
                                      (bin _⊠_ (sub (bin _⇛_ (nul Bool') (nul Bool')) σ) (nul Bool'))
                                      refl
                                      refl

example' : {Δ : Ctx C} {Γ : Ctx C} {Θ : Ctx C} →
           (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
           ((Bool' ⇛ Bool') ⊠ ((Discr Bool) [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
example' σ τ = by-naturality

-- Experiments interaction var + by-naturality tactics

not' : {Γ : Ctx C} → Tm Γ Bool' → Tm Γ Bool'
term (not' b) x _ = not (b ⟨ x , _ ⟩')
naturality (not' b) f eγ = cong not (naturality b f eγ)

not-fun : Tm {C = C} ◇ (Bool' ⇛ Bool')
not-fun = lam[ "b" ∈ Bool' ] ι[ by-naturality ] not' (ι[ by-naturality ] var "b")
