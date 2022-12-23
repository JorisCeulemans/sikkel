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
    C : BaseCategory


ClosedTy : BaseCategory → Set₁
ClosedTy C = {Γ : Ctx C} → Ty Γ

-- A "genuine" closed type should be natural.
-- I.e. it is a pseudonatural transformation from the terminal
-- pseudofunctor (from Ctx to Groupoids) to the pseudofunctor Ty.
record IsClosedNatural {C} (U : ClosedTy C) : Set₁ where
  field
    closed-natural : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) →
                     U [ σ ] ≅ᵗʸ U
    closed-id : {Γ : Ctx C} → closed-natural (id-subst Γ) ≅ᵉ ty-subst-id U
    closed-⊚ : {Γ Δ Θ : Ctx C} (σ : Δ ⇒ Θ) (τ : Γ ⇒ Δ) →
               (≅ᵗʸ-trans (ty-subst-cong-ty τ (closed-natural σ)) (closed-natural τ))
                 ≅ᵉ
               (≅ᵗʸ-trans (ty-subst-comp U σ τ) (closed-natural (σ ⊚ τ)))
    closed-subst-eq : {Γ Δ : Ctx C} {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) →
                      ≅ᵗʸ-trans (ty-subst-cong-subst ε U) (closed-natural τ) ≅ᵉ closed-natural σ

open IsClosedNatural {{...}} public


-- A type in the empty context gives rise to a closed type.
From-◇-ty : Ty {C = C} ◇ → ClosedTy C
From-◇-ty T {Γ = Γ} = T [ !◇ Γ ]

-- We are not declaring this as an instance because From-◇-ty is currently never used.
From-◇-ty-natural : (T : Ty {C = C} ◇) → IsClosedNatural (From-◇-ty T)
IsClosedNatural.closed-natural (From-◇-ty-natural T) σ = ≅ᵗʸ-trans (ty-subst-comp T _ σ) (ty-subst-cong-subst (◇-terminal _ _ _) T)
eq (from-eq (IsClosedNatural.closed-id (From-◇-ty-natural T))) _ = ty-id T
eq (from-eq (IsClosedNatural.closed-⊚ (From-◇-ty-natural {C} T) σ τ)) _ = ty-cong-2-1 T (BaseCategory.hom-idʳ C)
eq (from-eq (IsClosedNatural.closed-subst-eq (From-◇-ty-natural {C} T) ε)) _ = ty-cong-2-1 T (BaseCategory.hom-idʳ C)
