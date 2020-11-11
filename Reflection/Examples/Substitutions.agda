open import Categories

module Reflection.Examples.Substitutions {C : Category} where

open import Level
open import Relation.Binary.PropositionalEquality

open import CwF-Structure hiding (var)
open import Reflection.Substitutions
--open import Reflection.Helpers

private
  variable
    Δ Γ Θ Ξ : Ctx C

example : (ρ : Δ ⇒ Ξ) (σ : ◇ ⇒ Γ) (τ : Γ ⇒ Θ) → ((id-subst Θ ⊚ τ) ⊚ σ) ⊚ (!◇ Ξ ⊚ ρ) ≅ˢ τ ⊚ ((σ ⊚ id-subst ◇) ⊚ (!◇ Ξ ⊚ (id-subst Ξ ⊚ ρ)))
example ρ σ τ = subst-reflect (((val id' ⊚' val (var τ)) ⊚' val (var σ)) ⊚' (val !◇' ⊚' val (var ρ)))
                              (val (var τ) ⊚' ((val (var σ) ⊚' val id') ⊚' (val !◇' ⊚' (val id' ⊚' val (var ρ)))))
                              refl

example2 : (σ : Δ ⇒ Γ) → !◇ Γ ⊚ σ ≅ˢ id-subst ◇ ⊚ !◇ Δ
example2 σ = subst-reflect (val !◇' ⊚' val (var σ))
                           (val id' ⊚' val !◇')
                           refl
