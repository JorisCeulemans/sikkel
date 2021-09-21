--------------------------------------------------
-- Closed types (i.e. types that can be defined in any context)
--------------------------------------------------

module Model.CwF-Structure.ClosedType where

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Reflection.SubstitutionSequence

private
  variable
    C : Category


ClosedType : Category → Set₁
ClosedType C = {Γ : Ctx C} → Ty Γ

record IsClosedNatural {C} (U : ClosedType C) : Set₁ where
  field
    closed-natural : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) →
                     U [ σ ] ≅ᵗʸ U

open IsClosedNatural {{...}} public


-- A type in the empty context gives rise to a closed type.
From-◇-ty : Ty {C = C} ◇ → ClosedType C
From-◇-ty T {Γ = Γ} = T [ !◇ Γ ]

-- We are not declaring this as an instance because From-◇-ty is currently never used.
From-◇-ty-natural : (T : Ty {C = C} ◇) → IsClosedNatural (From-◇-ty T)
IsClosedNatural.closed-natural (From-◇-ty-natural T) σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼)
                                                                           (!◇ _ ◼)
                                                                           T
                                                                           (◇-terminal _ _ _)
