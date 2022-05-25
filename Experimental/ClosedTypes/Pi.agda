module Experimental.ClosedTypes.Pi where

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term
open import Model.CwF-Structure.Reflection.SubstitutionSequence

open import Experimental.ClosedTypes
open import Experimental.DependentTypes.Model.Function

private variable
  C : BaseCategory
  Δ Γ : Ctx C


-- Pi-types with a closed type as their domain.
sPi : (T : ClosedTy C) → Ty (Γ ,,ₛ T) → Ty Γ
sPi T S = Pi (T [ !◇ _ ]) S

sdλ[_]_ : (T : ClosedTy C) {S : Ty (Γ ,,ₛ T)} → Tm (Γ ,,ₛ T) S → Tm Γ (sPi T S)
sdλ[ T ] b = lam _ b

sap : {T : ClosedTy C} {S : Ty (Γ ,,ₛ T)} → Tm Γ (sPi T S) → Tm (Γ ,,ₛ T) S
sap f = ap f

sdapp : {T : ClosedTy C} {S : Ty (Γ ,,ₛ T)} →
        Tm Γ (sPi T S) → (t : SimpleTm Γ T) → Tm Γ (S [ id-subst Γ ,ₛ t ])
sdapp f t = sap f [ id-subst _ ,ₛ t ]'

sPi-natural : {T : ClosedTy C} {S : Ty (Γ ,,ₛ T)} (σ : Δ ⇒ Γ) →
              (sPi T S) [ σ ] ≅ᵗʸ sPi T (S [ σ s⊹ ])
sPi-natural {T = T} {S} σ =
  ≅ᵗʸ-trans (Pi-natural σ) (Pi-cong (closed-ty-natural T σ) (ty-subst-seq-cong (_ ◼) (_ ∷ _ ◼) S subst-eq-proof))
  where
    subst-eq-proof : _ ≅ˢ _
    eq subst-eq-proof δ = cong (func σ _ ,_) (sym (trans (ty-id T) (ty-id T)))

sPi-cong₂ : {T : ClosedTy C} {S1 S2 : Ty (Γ ,,ₛ T)} →
            S1 ≅ᵗʸ S2 → sPi T S1 ≅ᵗʸ sPi T S2
sPi-cong₂ {S2 = S2} eS =
  Pi-cong ≅ᵗʸ-refl (≅ᵗʸ-trans eS (≅ᵗʸ-sym (≅ᵗʸ-trans (ty-subst-cong-subst (record { eq = λ _ → refl }) S2) (ty-subst-id S2))))
