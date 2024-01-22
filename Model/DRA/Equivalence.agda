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
  no-eta-equality
  field
    from : TwoCell μ ρ
    to : TwoCell ρ μ
    isoˡ : to ⓣ-vert from ≅ᵗᶜ id-cell
    isoʳ : from ⓣ-vert to ≅ᵗᶜ id-cell
open _≅ᵈ_ public

reflᵈ : {μ : DRA C D} → μ ≅ᵈ μ
from reflᵈ = id-cell
to reflᵈ = id-cell
isoˡ reflᵈ = ⓣ-vert-unitˡ
isoʳ reflᵈ = ⓣ-vert-unitˡ

symᵈ : {μ ρ : DRA C D} → μ ≅ᵈ ρ → ρ ≅ᵈ μ
from (symᵈ ℯ) = to ℯ
to (symᵈ ℯ) = from ℯ
isoˡ (symᵈ ℯ) = isoʳ ℯ
isoʳ (symᵈ ℯ) = isoˡ ℯ

transᵈ : {μ ρ κ : DRA C D} → μ ≅ᵈ ρ → ρ ≅ᵈ κ → μ ≅ᵈ κ
from (transᵈ ℯ ℯ') = from ℯ' ⓣ-vert from ℯ
to (transᵈ ℯ ℯ') = to ℯ ⓣ-vert to ℯ'
isoˡ (transᵈ ℯ ℯ') = begin
    (to ℯ ⓣ-vert to ℯ') ⓣ-vert (from ℯ' ⓣ-vert from ℯ)
  ≅⟨ transᵗᶜ ⓣ-vert-assoc (ⓣ-vert-congʳ (symᵗᶜ ⓣ-vert-assoc)) ⟩
    to ℯ ⓣ-vert ((to ℯ' ⓣ-vert from ℯ') ⓣ-vert from ℯ)
  ≅⟨ ⓣ-vert-congʳ (ⓣ-vert-congˡ (isoˡ ℯ')) ⟩
    to ℯ ⓣ-vert (id-cell ⓣ-vert from ℯ)
  ≅⟨ ⓣ-vert-congʳ ⓣ-vert-unitˡ ⟩
    to ℯ ⓣ-vert from ℯ
  ≅⟨ isoˡ ℯ ⟩
    id-cell ∎
  where open ≅ᵗᶜ-Reasoning
isoʳ (transᵈ ℯ ℯ') = begin
    (from ℯ' ⓣ-vert from ℯ) ⓣ-vert (to ℯ ⓣ-vert to ℯ')
  ≅⟨ transᵗᶜ ⓣ-vert-assoc (ⓣ-vert-congʳ (symᵗᶜ ⓣ-vert-assoc)) ⟩
    from ℯ' ⓣ-vert ((from ℯ ⓣ-vert to ℯ) ⓣ-vert to ℯ')
  ≅⟨ ⓣ-vert-congʳ (ⓣ-vert-congˡ (isoʳ ℯ)) ⟩
    from ℯ' ⓣ-vert (id-cell ⓣ-vert to ℯ')
  ≅⟨ ⓣ-vert-congʳ ⓣ-vert-unitˡ ⟩
    from ℯ' ⓣ-vert to ℯ'
  ≅⟨ isoʳ ℯ' ⟩
    id-cell ∎
  where open ≅ᵗᶜ-Reasoning

lock-iso : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ : Ctx D} → Γ ,lock⟨ μ ⟩ ≅ᶜ Γ ,lock⟨ ρ ⟩
from (lock-iso ℯ) = key-subst (to ℯ)
to (lock-iso ℯ) = key-subst (from ℯ)
isoˡ (lock-iso ℯ) = key-subst-eq (isoˡ ℯ)
isoʳ (lock-iso ℯ) = key-subst-eq (isoʳ ℯ)

eq-dra-tyʳ : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ : Ctx D} (T : Ty (Γ ,lock⟨ μ ⟩)) →
             ⟨ μ ∣ T ⟩ ≅ᵗʸ ⟨ ρ ∣ T [ key-subst (from ℯ) ] ⟩
from (eq-dra-tyʳ ℯ T) = coe-trans (from ℯ)
to (eq-dra-tyʳ {μ = μ} ℯ T) = dra-map μ (from (ty-subst-cong-subst-2-0 T (key-subst-eq (isoˡ ℯ)))) ⊙ coe-trans (to ℯ)
isoˡ (eq-dra-tyʳ {μ = μ} ℯ T) = begin
    (dra-map μ (from (ty-subst-cong-subst-2-0 T (key-subst-eq (isoˡ ℯ)))) ⊙ coe-trans (to ℯ)) ⊙ coe-trans (from ℯ)
  ≅⟨ ⊙-congˡ (⊙-congˡ (transⁿ (dra-map-⊙ μ) (⊙-congʳ (dra-map-⊙ μ)))) ⟩
    _
  ≅⟨ transⁿ (transⁿ (⊙-congˡ (⊙-congˡ (symⁿ ⊙-assoc))) (⊙-congˡ ⊙-assoc)) ⊙-assoc ⟩
    dra-map μ (from (ty-subst-id T))
    ⊙ dra-map μ (from (ty-subst-cong-subst (key-subst-eq (isoˡ ℯ)) T))
    ⊙ ((dra-map μ (from (ty-subst-comp T (transf-op (transf (from ℯ)) _) (transf-op (transf (to ℯ)) _)))
        ⊙ coe-trans (to ℯ)
        )
      ⊙ coe-trans (from ℯ)
      )
  ≅⟨ ⊙-congʳ coe-trans-ⓣ ⟨
    _
  ≅⟨ ⊙-assoc ⟩
    dra-map μ (from (ty-subst-id T))
    ⊙ (dra-map μ (from (ty-subst-cong-subst (key-subst-eq (isoˡ ℯ)) T))
      ⊙ coe-trans (to ℯ ⓣ-vert from ℯ)
      )
  ≅⟨ ⊙-congʳ (coe-trans-cong (isoˡ ℯ)) ⟩
    dra-map μ (from (ty-subst-id T)) ⊙ coe-trans {μ = μ} id-cell
  ≅⟨ ⊙-congʳ (coe-trans-id μ) ⟩
    dra-map μ (from (ty-subst-id T)) ⊙ dra-map μ (ty-subst-id-to T)
  ≅⟨ dra-map-cong-2-0 μ (ty-subst-id-from-to T) ⟩
    id-trans ⟨ μ ∣ T ⟩ ∎
  where open ≅ⁿ-Reasoning
isoʳ (eq-dra-tyʳ {μ = μ}{ρ} ℯ T) = begin
    coe-trans (from ℯ)
    ⊙ (dra-map μ (from (ty-subst-cong-subst-2-0 T (key-subst-eq (isoˡ ℯ))))
      ⊙ coe-trans (to ℯ)
      )
  ≅⟨ ⊙-assoc ⟨
    _
  ≅⟨ ⊙-congˡ (coe-trans-natural (from ℯ) _) ⟨
    dra-map ρ (ty-subst-map (key-subst (from ℯ)) (from (ty-subst-cong-subst-2-0 T (key-subst-eq (isoˡ ℯ)))))
    ⊙ coe-trans (from ℯ)
    ⊙ coe-trans (to ℯ)
  ≅⟨ ⊙-congˡ (⊙-congˡ (dra-map-cong ρ (from-eq (ty-subst-cong-subst-2-0-iso T _ _)))) ⟩
    dra-map ρ (from (ty-subst-cong-subst-2-0 (T [ key-subst (from ℯ) ]) (key-subst-eq (isoʳ ℯ))))
    ⊙ coe-trans (from ℯ)
    ⊙ coe-trans (to ℯ)
  ≅⟨ ⊙-congˡ (⊙-congˡ (transⁿ (dra-map-⊙ ρ) (transⁿ (⊙-congʳ (dra-map-⊙ ρ)) (symⁿ ⊙-assoc)))) ⟩
    _
  ≅⟨ transⁿ (⊙-congˡ ⊙-assoc) ⊙-assoc ⟩
    _
  ≅⟨ ⊙-congʳ coe-trans-ⓣ ⟨
    _
  ≅⟨ ⊙-assoc ⟩
    dra-map ρ (from (ty-subst-id (T [ key-subst (from ℯ) ])))
    ⊙ (dra-map ρ (from (ty-subst-cong-subst (key-subst-eq (isoʳ ℯ)) (T [ key-subst (from ℯ) ])))
      ⊙ coe-trans (from ℯ ⓣ-vert to ℯ)
      )
  ≅⟨ ⊙-congʳ (coe-trans-cong (isoʳ ℯ)) ⟩
    dra-map ρ (from (ty-subst-id (T [ key-subst (from ℯ) ])))
    ⊙ coe-trans (id-cell {μ = ρ})
  ≅⟨ ⊙-congʳ (coe-trans-id ρ) ⟩
    dra-map ρ (from (ty-subst-id (T [ key-subst (from ℯ) ])))
    ⊙ dra-map ρ (ty-subst-id-to (T [ key-subst (from ℯ) ]))
  ≅⟨ dra-map-cong-2-0 ρ (ty-subst-id-from-to (T [ key-subst (from ℯ) ])) ⟩
    id-trans ⟨ ρ ∣ T [ key-subst (from ℯ) ] ⟩ ∎
  where open ≅ⁿ-Reasoning

eq-dra-tyʳ-map : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ : Ctx D} {T S : Ty (Γ ,lock⟨ μ ⟩)} (φ : T ↣ S) →
                 dra-map ρ (ty-subst-map (key-subst (from ℯ)) φ) ⊙ from (eq-dra-tyʳ ℯ T)
                   ≅ⁿ
                 from (eq-dra-tyʳ ℯ S) ⊙ dra-map μ φ
eq-dra-tyʳ-map ℯ φ = coe-trans-natural (from ℯ) φ

eq-dra-tyʳ-cong : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ : Ctx D} {T S : Ty (Γ ,lock⟨ μ ⟩)} (e : T ≅ᵗʸ S) →
                  transᵗʸ (eq-dra-tyʳ ℯ T) (dra-cong ρ (ty-subst-cong-ty (key-subst (from ℯ)) e))
                    ≅ᵉ
                  transᵗʸ (dra-cong μ e) (eq-dra-tyʳ ℯ S)
from-eq (eq-dra-tyʳ-cong ℯ e) = eq-dra-tyʳ-map ℯ (from e)

eq-dra-tyʳ-from-natural : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T : Ty (Δ ,lock⟨ μ ⟩)} →
                          dra-map ρ (from (ty-subst-cong-subst-2-2 T (key-subst-natural (from ℯ))))
                          ⊙ from (dra-natural ρ σ)
                          ⊙ ty-subst-map σ (from (eq-dra-tyʳ ℯ T))
                            ≅ⁿ
                          from (eq-dra-tyʳ ℯ (T [ lock-fmap μ σ ]))
                          ⊙ from (dra-natural μ σ)
eq-dra-tyʳ-from-natural ℯ σ = coe-trans-dra-natural (from ℯ) σ

eq-dra-tyʳ-natural : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T : Ty (Δ ,lock⟨ μ ⟩)} →
                     transᵗʸ (ty-subst-cong-ty σ (eq-dra-tyʳ ℯ T)) (transᵗʸ (dra-natural ρ σ) (dra-cong ρ (ty-subst-cong-subst-2-2 T (key-subst-natural (from ℯ)))))
                       ≅ᵉ
                     transᵗʸ (dra-natural μ σ) (eq-dra-tyʳ ℯ (T [ lock-fmap μ σ ]))
from-eq (eq-dra-tyʳ-natural ℯ σ) = eq-dra-tyʳ-from-natural ℯ σ

eq-dra-tyˡ : {μ ρ : DRA C D} (ℯ : μ ≅ᵈ ρ) {Γ : Ctx D} (T : Ty (lock ρ Γ)) →
             ⟨ μ ∣ T [ key-subst (to ℯ) ] ⟩ ≅ᵗʸ ⟨ ρ ∣ T ⟩
eq-dra-tyˡ ℯ T = symᵗʸ (eq-dra-tyʳ (symᵈ ℯ) T)

eq-dra-closed : {μ ρ : DRA C D} → μ ≅ᵈ ρ →
                {A : ClosedTy C} → IsClosedNatural A →
                {Γ : Ctx D} →
                ⟨ μ ∣ A {Γ ,lock⟨ μ ⟩} ⟩ ≅ᵗʸ ⟨ ρ ∣ A ⟩
eq-dra-closed {ρ = ρ} ℯ {A} clA = transᵗʸ (eq-dra-tyʳ ℯ A) (dra-cong ρ (closed-natural clA _))


𝟙-unitʳ : (μ : DRA C D) → μ ⓓ 𝟙 ≅ᵈ μ
transf-op (transf (from (𝟙-unitʳ μ))) _ = id-subst _
eq (naturality (transf (from (𝟙-unitʳ μ))) _) _ = refl
transf-op (transf (to (𝟙-unitʳ μ))) _ = id-subst _
eq (naturality (transf (to (𝟙-unitʳ μ))) _) _ = refl
eq (key-subst-eq (isoˡ (𝟙-unitʳ μ))) _ = refl
eq (key-subst-eq (isoʳ (𝟙-unitʳ μ))) _ = refl

𝟙-unitˡ : (μ : DRA C D) → 𝟙 ⓓ μ ≅ᵈ μ
transf-op (transf (from (𝟙-unitˡ μ))) _ = id-subst _
eq (naturality (transf (from (𝟙-unitˡ μ))) _) _ = refl
transf-op (transf (to (𝟙-unitˡ μ))) _ = id-subst _
eq (naturality (transf (to (𝟙-unitˡ μ))) _) _ = refl
eq (key-subst-eq (isoˡ (𝟙-unitˡ μ))) _ = refl
eq (key-subst-eq (isoʳ (𝟙-unitˡ μ))) _ = refl

ⓓ-assoc : {C₁ C₂ C₃ C₄ : BaseCategory}
           (μ₃₄ : DRA C₃ C₄) (μ₂₃ : DRA C₂ C₃) (μ₁₂ : DRA C₁ C₂) →
           (μ₃₄ ⓓ μ₂₃) ⓓ μ₁₂ ≅ᵈ μ₃₄ ⓓ (μ₂₃ ⓓ μ₁₂)
transf-op (transf (from (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂))) _ = id-subst _
eq (naturality (transf (from (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂))) _) _ = refl
transf-op (transf (to (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂))) _ = id-subst _
eq (naturality (transf (to (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂))) _) _ = refl
eq (key-subst-eq (isoˡ (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂))) _ = refl
eq (key-subst-eq (isoʳ (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂))) _ = refl

ⓓ-congʳ : (ρ : DRA D E) {μ μ' : DRA C D} → μ ≅ᵈ μ' → ρ ⓓ μ ≅ᵈ ρ ⓓ μ'
from (ⓓ-congʳ ρ ℯ) = id-cell ⓣ-hor from ℯ
to (ⓓ-congʳ ρ ℯ) = id-cell ⓣ-hor to ℯ
isoˡ (ⓓ-congʳ ρ ℯ) = begin
    (id-cell ⓣ-hor to ℯ) ⓣ-vert (id-cell ⓣ-hor from ℯ)
  ≅⟨ 2-cell-interchange ⟨
    (id-cell ⓣ-vert id-cell) ⓣ-hor (to ℯ ⓣ-vert from ℯ)
  ≅⟨ ⓣ-hor-cong ⓣ-vert-unitʳ (isoˡ ℯ) ⟩
    id-cell ⓣ-hor id-cell
  ≅⟨ ⓣ-hor-id ⟩
    id-cell ∎
  where open ≅ᵗᶜ-Reasoning
isoʳ (ⓓ-congʳ ρ ℯ) = begin
    (id-cell ⓣ-hor from ℯ) ⓣ-vert (id-cell ⓣ-hor to ℯ)
  ≅⟨ 2-cell-interchange ⟨
    (id-cell ⓣ-vert id-cell) ⓣ-hor (from ℯ ⓣ-vert to ℯ)
  ≅⟨ ⓣ-hor-cong ⓣ-vert-unitʳ (isoʳ ℯ) ⟩
    id-cell ⓣ-hor id-cell
  ≅⟨ ⓣ-hor-id ⟩
    id-cell ∎
  where open ≅ᵗᶜ-Reasoning

ⓓ-congˡ : {ρ ρ' : DRA D E} (μ : DRA C D) → ρ ≅ᵈ ρ' → ρ ⓓ μ ≅ᵈ ρ' ⓓ μ
from (ⓓ-congˡ μ ℯ) = from ℯ ⓣ-hor id-cell
to (ⓓ-congˡ μ ℯ) = to ℯ ⓣ-hor id-cell
isoˡ (ⓓ-congˡ μ ℯ) = begin
    (to ℯ ⓣ-hor id-cell) ⓣ-vert (from ℯ ⓣ-hor id-cell)
  ≅⟨ 2-cell-interchange ⟨
    (to ℯ ⓣ-vert from ℯ) ⓣ-hor (id-cell ⓣ-vert id-cell)
  ≅⟨ ⓣ-hor-cong (isoˡ ℯ) ⓣ-vert-unitʳ ⟩
    id-cell ⓣ-hor id-cell
  ≅⟨ ⓣ-hor-id ⟩
    id-cell ∎
  where open ≅ᵗᶜ-Reasoning
isoʳ (ⓓ-congˡ μ ℯ) = begin
    (from ℯ ⓣ-hor id-cell) ⓣ-vert (to ℯ ⓣ-hor id-cell)
  ≅⟨ 2-cell-interchange ⟨
    (from ℯ ⓣ-vert to ℯ) ⓣ-hor (id-cell ⓣ-vert id-cell)
  ≅⟨ ⓣ-hor-cong (isoʳ ℯ) ⓣ-vert-unitʳ ⟩
    id-cell ⓣ-hor id-cell
  ≅⟨ ⓣ-hor-id ⟩
    id-cell ∎
  where open ≅ᵗᶜ-Reasoning


-- There is no module ≅ᵈ-Reasoning because DRA C D with _≅ᵈ_ is a groupoid and not
-- a setoid. Hence we do not want to add reflᵈ to the end of every
-- proof of type equivalence.



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
