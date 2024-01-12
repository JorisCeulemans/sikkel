-- Definition of some operations which are not in the standard library

module Preliminaries where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Definitions
open import Relation.Binary.Reasoning.Syntax

private
  variable
    a ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C : Set a


-- Extension of syntax for reasoning combinators to include the ones for ≅.
module ≅-syntax
  {R : REL A B ℓ₂}
  (S : REL B C ℓ₁)
  (T : REL A C ℓ₃)
  (step : Trans R S T)
  {U : REL B A ℓ₄}
  (sym : Sym U R)
  where

  infixr 2 step-≅-⟩ step-≅-⟨ step-≅-∣
  step-≅-⟩ = forward S T step
  step-≅-⟨ = backward S T step sym

  step-≅-∣ : ∀ x {y} → R x y → R x y
  step-≅-∣ x xRy = xRy

  syntax step-≅-⟩ x yRz x≅y = x ≅⟨ x≅y ⟩ yRz
  syntax step-≅-⟨ x yRz y≅x = x ≅⟨ y≅x ⟨ yRz
  syntax step-≅-∣ x xRy     = x ≅⟨⟩ xRy
