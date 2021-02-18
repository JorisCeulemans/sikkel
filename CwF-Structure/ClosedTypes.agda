--------------------------------------------------
-- Closed types (i.e. types that can be defined in any context)
--------------------------------------------------

module CwF-Structure.ClosedTypes where

open import Level

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.SubstitutionSequence

private
  variable
    ℓ : Level
    C : Category


ClosedType : Category → (Level → Level) → Setω
ClosedType C f = ∀ {ℓc} {Γ : Ctx C ℓc} → Ty Γ (f ℓc)

record IsClosedNatural {C} {ℓ} (U : ClosedType C ℓ) : Setω where
  field
    closed-natural : ∀ {ℓc ℓc'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                     U [ σ ] ≅ᵗʸ U

open IsClosedNatural {{...}} public


-- A type in the empty context gives rise to a closed type.
From-◇-ty : Ty {C = C} ◇ ℓ → ClosedType C (λ _ → ℓ)
From-◇-ty T {Γ = Γ} = T [ !◇ Γ ]

-- We are not declaring this as an instance because From-◇-ty is currently never used.
From-◇-ty-natural : (T : Ty {C = C} ◇ ℓ) → IsClosedNatural (From-◇-ty T)
IsClosedNatural.closed-natural (From-◇-ty-natural T) σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼)
                                                                           (!◇ _ ◼)
                                                                           T
                                                                           (◇-terminal _ _ _)
