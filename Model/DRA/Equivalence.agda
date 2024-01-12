--------------------------------------------------
-- Equivalence of modalities
--------------------------------------------------

module Model.DRA.Equivalence where

open import Model.DRA.Basics
open import Model.DRA.TwoCell

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure

private
  variable
    C D E : BaseCategory

infix 1 _≅ᵈ_


record _≅ᵈ_  {C D} (μ ρ : DRA C D) : Set₁ where
  field
    eq-lock : (Γ : Ctx D) → Γ ,lock⟨ μ ⟩ ≅ᶜ Γ ,lock⟨ ρ ⟩
    eq-lock-natural-to : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) →
                         to (eq-lock Γ) ⊚ lock-fmap ρ σ ≅ˢ lock-fmap μ σ ⊚ to (eq-lock Δ)
    eq-dra-tyʳ : {Γ : Ctx D} (T : Ty (Γ ,lock⟨ μ ⟩)) → ⟨ μ ∣ T ⟩ ≅ᵗʸ ⟨ ρ ∣ T [ to (eq-lock Γ) ] ⟩

    -- In the future, we will probably need an equivalence requirement for the modal term former,
    --  such as the following. For simplicity, we currently omit this.
    {-eq-mod-introʳ : {Γ : Ctx D} {T : Ty (lock μ Γ)} (t : Tm (lock μ Γ) T) →
                   mod-intro μ t ≅ᵗᵐ ι[ eq-mod-tyʳ T ] mod-intro ρ (t [ to (eq-lock Γ) ]')-}

  eq-lock-natural-from : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) →
                         from (eq-lock Γ) ⊚ lock-fmap μ σ ≅ˢ lock-fmap ρ σ ⊚ from (eq-lock Δ)
  eq-lock-natural-from {Δ} {Γ} σ = begin
      from (eq-lock Γ) ⊚ lock-fmap μ σ
    ≅⟨ id-subst-unitʳ _ ⟨
      (from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ id-subst (lock μ Δ)
    ≅⟨ ⊚-congʳ (isoˡ (eq-lock Δ)) ⟨
      (from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ (to (eq-lock Δ) ⊚ from (eq-lock Δ))
    ≅⟨ ⊚-assoc ⟨
      ((from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ to (eq-lock Δ)) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ ⊚-assoc ⟩
      (from (eq-lock Γ) ⊚ (lock-fmap μ σ ⊚ to (eq-lock Δ))) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ (⊚-congʳ (eq-lock-natural-to σ)) ⟨
      (from (eq-lock Γ) ⊚ (to (eq-lock Γ) ⊚ lock-fmap ρ σ)) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ ⊚-assoc ⟨
      ((from (eq-lock Γ) ⊚ to (eq-lock Γ)) ⊚ lock-fmap ρ σ) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ (⊚-congˡ (isoʳ (eq-lock Γ))) ⟩
      (id-subst (lock ρ Γ) ⊚ lock-fmap ρ σ) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ (id-subst-unitˡ _) ⟩
      lock-fmap ρ σ ⊚ from (eq-lock Δ) ∎
    where open ≅ˢ-Reasoning

  eq-dra-tyˡ : {Γ : Ctx D} (T : Ty (lock ρ Γ)) → ⟨ μ ∣ T [ from (eq-lock Γ) ] ⟩ ≅ᵗʸ ⟨ ρ ∣ T ⟩
  eq-dra-tyˡ {Γ = Γ} T =
    transᵗʸ (eq-dra-tyʳ (T [ from (eq-lock Γ) ])) (
    transᵗʸ (dra-cong ρ (ty-subst-cong-subst-2-1 T (isoʳ (eq-lock Γ)))) (
    dra-cong ρ (ty-subst-id T)))

  eq-dra-closed : {A : ClosedTy C} → IsClosedNatural A → {Γ : Ctx D} → ⟨ μ ∣ A {Γ ,lock⟨ μ ⟩} ⟩ ≅ᵗʸ ⟨ ρ ∣ A ⟩
  eq-dra-closed {A = A} clA =
    transᵗʸ (eq-dra-tyʳ A) (dra-cong ρ (closed-natural clA (to (eq-lock _))))

open _≅ᵈ_ public

reflᵈ : ∀ {C D} → {μ : DRA C D} → μ ≅ᵈ μ
eq-lock (reflᵈ {μ = μ}) Γ = reflᶜ
eq-lock-natural-to (reflᵈ {μ = μ}) σ = transˢ (id-subst-unitˡ _) (symˢ (id-subst-unitʳ _))
eq-dra-tyʳ (reflᵈ {μ = μ}) T = dra-cong μ (symᵗʸ (ty-subst-id T))

symᵈ : ∀ {C D} {μ ρ : DRA C D} → μ ≅ᵈ ρ → ρ ≅ᵈ μ
eq-lock (symᵈ e) Γ = symᶜ (eq-lock e Γ)
eq-lock-natural-to (symᵈ e) σ = eq-lock-natural-from e σ
eq-dra-tyʳ (symᵈ e) T = symᵗʸ (eq-dra-tyˡ e T)

transᵈ : ∀ {C D} {μ ρ κ : DRA C D} → μ ≅ᵈ ρ → ρ ≅ᵈ κ → μ ≅ᵈ κ
eq-lock (transᵈ μ=ρ ρ=κ) Γ = transᶜ (eq-lock μ=ρ Γ) (eq-lock ρ=κ Γ)
eq-lock-natural-to (transᵈ {μ = μ} {ρ} {κ} μ=ρ ρ=κ) σ = begin
    (to (eq-lock μ=ρ _) ⊚ to (eq-lock ρ=κ _)) ⊚ lock-fmap κ σ
  ≅⟨ ⊚-assoc ⟩
    to (eq-lock μ=ρ _) ⊚ (to (eq-lock ρ=κ _) ⊚ lock-fmap κ σ)
  ≅⟨ ⊚-congʳ (eq-lock-natural-to ρ=κ σ) ⟩
    to (eq-lock μ=ρ _) ⊚ (lock-fmap ρ σ ⊚ to (eq-lock ρ=κ _))
  ≅⟨ ⊚-assoc ⟨
    (to (eq-lock μ=ρ _) ⊚ lock-fmap ρ σ) ⊚ to (eq-lock ρ=κ _)
  ≅⟨ ⊚-congˡ (eq-lock-natural-to μ=ρ σ) ⟩
    (lock-fmap μ σ ⊚ to (eq-lock μ=ρ _)) ⊚ to (eq-lock ρ=κ _)
  ≅⟨ ⊚-assoc ⟩
    lock-fmap μ σ ⊚ (to (eq-lock μ=ρ _) ⊚ to (eq-lock ρ=κ _)) ∎
  where open ≅ˢ-Reasoning
eq-dra-tyʳ (transᵈ {μ = μ} {ρ = ρ} {κ = κ} μ=ρ ρ=κ) {Γ = Γ} T =
  transᵗʸ (eq-dra-tyʳ μ=ρ T) (
  transᵗʸ (eq-dra-tyʳ ρ=κ (T [ to (eq-lock μ=ρ Γ) ])) (
  dra-cong κ (ty-subst-comp T _ _)))

𝟙-unitʳ : (μ : DRA C D) → μ ⓓ 𝟙 ≅ᵈ μ
eq-lock (𝟙-unitʳ μ) Γ = reflᶜ
eq (eq-lock-natural-to (𝟙-unitʳ μ) σ) _ = refl
eq-dra-tyʳ (𝟙-unitʳ μ) T = symᵗʸ (dra-cong μ (ty-subst-id T))

𝟙-unitˡ : (μ : DRA C D) → 𝟙 ⓓ μ ≅ᵈ μ
eq-lock (𝟙-unitˡ μ) Γ = reflᶜ
eq (eq-lock-natural-to (𝟙-unitˡ μ) σ) _ = refl
eq-dra-tyʳ (𝟙-unitˡ μ) T = symᵗʸ (dra-cong μ (ty-subst-id T))

ⓓ-assoc : {C₁ C₂ C₃ C₄ : BaseCategory}
           (μ₃₄ : DRA C₃ C₄) (μ₂₃ : DRA C₂ C₃) (μ₁₂ : DRA C₁ C₂) →
           (μ₃₄ ⓓ μ₂₃) ⓓ μ₁₂ ≅ᵈ μ₃₄ ⓓ (μ₂₃ ⓓ μ₁₂)
eq-lock (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂) Γ = reflᶜ
eq (eq-lock-natural-to (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂) σ) _ = refl
eq-dra-tyʳ (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂) T = symᵗʸ (dra-cong μ₃₄ (dra-cong μ₂₃ (dra-cong μ₁₂ (ty-subst-id T))))

ⓓ-congʳ : (ρ : DRA D E) {μ μ' : DRA C D} → μ ≅ᵈ μ' → ρ ⓓ μ ≅ᵈ ρ ⓓ μ'
eq-lock (ⓓ-congʳ ρ μ=μ') Γ = eq-lock μ=μ' (Γ ,lock⟨ ρ ⟩)
eq-lock-natural-to (ⓓ-congʳ ρ {μ} {μ'} μ=μ') σ = eq-lock-natural-to μ=μ' (lock-fmap ρ σ)
eq-dra-tyʳ (ⓓ-congʳ ρ μ=μ') T = dra-cong ρ (eq-dra-tyʳ μ=μ' T)

ⓓ-congˡ : {ρ ρ' : DRA D E} (μ : DRA C D) → ρ ≅ᵈ ρ' → ρ ⓓ μ ≅ᵈ ρ' ⓓ μ
from (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = lock-fmap μ (from (eq-lock ρ=ρ' Γ))
to (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = lock-fmap μ (to (eq-lock ρ=ρ' Γ))
isoˡ (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoˡ (eq-lock ρ=ρ' Γ))
isoʳ (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoʳ (eq-lock ρ=ρ' Γ))
eq-lock-natural-to (ⓓ-congˡ {ρ = ρ} {ρ'} μ ρ=ρ') σ = begin
    lock-fmap μ (to (eq-lock ρ=ρ' _)) ⊚ lock-fmap μ (lock-fmap ρ' σ)
  ≅⟨ lock-fmap-⊚ μ _ _ ⟨
    lock-fmap μ (to (eq-lock ρ=ρ' _) ⊚ lock-fmap ρ' σ)
  ≅⟨ lock-fmap-cong μ (eq-lock-natural-to ρ=ρ' σ) ⟩
    lock-fmap μ (lock-fmap ρ σ ⊚ to (eq-lock ρ=ρ' _))
  ≅⟨ lock-fmap-⊚ μ _ _ ⟩
    lock-fmap μ (lock-fmap ρ σ) ⊚ lock-fmap μ (to (eq-lock ρ=ρ' _)) ∎
  where open ≅ˢ-Reasoning
eq-dra-tyʳ (ⓓ-congˡ {ρ = ρ} {ρ' = ρ'} μ ρ=ρ') {Γ = Γ} T =
  transᵗʸ (eq-dra-tyʳ ρ=ρ' ⟨ μ ∣ T ⟩) (dra-cong ρ' (dra-natural μ (to (eq-lock ρ=ρ' Γ))))

-- There is no module ≅ᵈ-Reasoning because DRA C D with _≅ᵈ_ is a groupoid and not
-- a setoid. Hence we do not want to add reflᵈ to the end of every
-- proof of type equivalence.


≅ᵈ-to-2-cell : {μ ρ : DRA C D} → μ ≅ᵈ ρ → TwoCell μ ρ
transf-op (transf (≅ᵈ-to-2-cell μ=ρ)) Γ = to (eq-lock μ=ρ Γ)
naturality (transf (≅ᵈ-to-2-cell μ=ρ)) = eq-lock-natural-to μ=ρ

ⓣ-hor-unitˡ : {μ ρ : DRA C D} {α : TwoCell μ ρ} →
              ≅ᵈ-to-2-cell (𝟙-unitˡ ρ) ⓣ-vert (id-cell {μ = 𝟙} ⓣ-hor α) ≅ᵗᶜ α ⓣ-vert ≅ᵈ-to-2-cell (𝟙-unitˡ μ)
key-subst-eq (ⓣ-hor-unitˡ {ρ = ρ}) =
  transˢ (id-subst-unitʳ _) (transˢ (⊚-congʳ (lock-fmap-id ρ)) (transˢ (id-subst-unitʳ _) (symˢ (id-subst-unitˡ _))))

ⓣ-hor-unitʳ : {μ ρ : DRA C D} {α : TwoCell μ ρ} →
              ≅ᵈ-to-2-cell (𝟙-unitʳ ρ) ⓣ-vert (α ⓣ-hor id-cell {μ = 𝟙}) ≅ᵗᶜ α ⓣ-vert ≅ᵈ-to-2-cell (𝟙-unitʳ μ)
key-subst-eq (ⓣ-hor-unitʳ {ρ = ρ}) = id-subst-unitʳ _

ⓣ-hor-assoc : {F : BaseCategory}
              {μ μ' : DRA C D} {ρ ρ' : DRA D E} {κ κ' : DRA E F}
              {α : TwoCell μ μ'} {β : TwoCell ρ ρ'} {γ : TwoCell κ κ'} →
              ≅ᵈ-to-2-cell (ⓓ-assoc _ _ _) ⓣ-vert ((γ ⓣ-hor β) ⓣ-hor α) ≅ᵗᶜ (γ ⓣ-hor (β ⓣ-hor α)) ⓣ-vert ≅ᵈ-to-2-cell (ⓓ-assoc _ _ _)
key-subst-eq (ⓣ-hor-assoc {μ' = μ'}) =
  transˢ (id-subst-unitʳ _) (transˢ (⊚-congʳ (lock-fmap-⊚ μ' _ _)) (transˢ (symˢ ⊚-assoc) (symˢ (id-subst-unitˡ _))))
