--------------------------------------------------
-- Two-cells between DRAs
--------------------------------------------------

module Model.DRA.TwoCell where

open import Model.DRA.Basics

open import Model.BaseCategory
open import Model.CwF-Structure

private
  variable
    C D E : BaseCategory

infix 1 _≅ᵗᶜ_
infixl 20 _ⓣ-vert_ _ⓣ-hor_


--------------------------------------------------
-- Definition of a two-cell as a natural transformations between the underlying context functors

-- TwoCell is defined as a record type so that Agda can better infer the two endpoint
--   modalities, e.g. in coe-ty.
record TwoCell (μ ρ : DRA C D) : Set₁ where
  constructor two-cell
  field
    transf : CtxNatTransf (ctx-functor ρ) (ctx-functor μ)

  key-subst : {Γ : Ctx D} → Γ ,lock⟨ ρ ⟩ ⇒ Γ ,lock⟨ μ ⟩
  key-subst {Γ = Γ} = transf-op transf Γ

  key-subst-natural : {Γ Δ : Ctx D} {σ : Γ ⇒ Δ} → key-subst {Δ} ⊚ lock-fmap ρ σ ≅ˢ lock-fmap μ σ ⊚ key-subst {Γ}
  key-subst-natural {σ = σ} = naturality transf σ

  coe : {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T [ key-subst ] ⟩
  coe t = dra-intro ρ ((dra-elim μ t) [ key-subst ]')

  coe-closed : {T : ClosedTy C} → IsClosedNatural T → {Γ : Ctx D} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
  coe-closed {T = T} clT t = ι⁻¹[ dra-cong ρ (closed-natural clT key-subst) ] coe t

open TwoCell public


-- The identity 2-cell
id-cell : {μ : DRA C D} → TwoCell μ μ
transf id-cell = id-ctx-transf _

-- Composition of 2-cells (both vertical and horizontal)
_ⓣ-vert_ : {μ ρ κ : DRA C D} → TwoCell μ ρ → TwoCell κ μ → TwoCell κ ρ
transf (α ⓣ-vert β) = transf β ⓝ-vert transf α

_ⓣ-hor_ : {μ μ' : DRA D E} {ρ ρ' : DRA C D} → TwoCell μ μ' → TwoCell ρ ρ' → TwoCell (μ ⓓ ρ) (μ' ⓓ ρ')
transf (α ⓣ-hor β) = transf β ⓝ-hor transf α


--------------------------------------------------
-- Equivalence of two-cells (i.e. equivalence of the underlying natural transformations)

record _≅ᵗᶜ_ {μ ρ : DRA C D} (α β : TwoCell μ ρ) : Set₁ where
  field
    key-subst-eq : ∀ {Γ} → key-subst α {Γ} ≅ˢ key-subst β
open _≅ᵗᶜ_ public

module _ {μ ρ : DRA C D} where
  reflᵗᶜ : {α : TwoCell μ ρ} → α ≅ᵗᶜ α
  key-subst-eq reflᵗᶜ = reflˢ

  symᵗᶜ : {α β : TwoCell μ ρ} → α ≅ᵗᶜ β → β ≅ᵗᶜ α
  key-subst-eq (symᵗᶜ α=β) = symˢ (key-subst-eq α=β)

  transᵗᶜ : {α1 α2 α3 : TwoCell μ ρ} → α1 ≅ᵗᶜ α2 → α2 ≅ᵗᶜ α3 → α1 ≅ᵗᶜ α3
  key-subst-eq (transᵗᶜ e e') = transˢ (key-subst-eq e) (key-subst-eq e')

  ⓣ-vert-unitˡ : {α : TwoCell μ ρ} → id-cell ⓣ-vert α ≅ᵗᶜ α
  key-subst-eq ⓣ-vert-unitˡ = id-subst-unitʳ _

  ⓣ-vert-unitʳ : {α : TwoCell μ ρ} → α ⓣ-vert id-cell ≅ᵗᶜ α
  key-subst-eq ⓣ-vert-unitʳ = id-subst-unitˡ _

ⓣ-vert-assoc : {μ ρ κ φ : DRA C D} {α : TwoCell μ ρ} {β : TwoCell ρ κ} {γ : TwoCell κ φ} →
               (γ ⓣ-vert β) ⓣ-vert α ≅ᵗᶜ γ ⓣ-vert (β ⓣ-vert α)
key-subst-eq ⓣ-vert-assoc = symˢ ⊚-assoc

ⓣ-vert-congˡ : {μ ρ κ : DRA C D} {α α' : TwoCell ρ κ} {β : TwoCell μ ρ} →
               α ≅ᵗᶜ α' → α ⓣ-vert β ≅ᵗᶜ α' ⓣ-vert β
key-subst-eq (ⓣ-vert-congˡ e) = ⊚-congʳ (key-subst-eq e)

ⓣ-vert-congʳ : {μ ρ κ : DRA C D} {α : TwoCell ρ κ} {β β' : TwoCell μ ρ} →
               β ≅ᵗᶜ β' → α ⓣ-vert β ≅ᵗᶜ α ⓣ-vert β'
key-subst-eq (ⓣ-vert-congʳ e) = ⊚-congˡ (key-subst-eq e)

ⓣ-hor-congˡ : {μ ρ : DRA C D} {κ φ : DRA D E} {α : TwoCell μ ρ} {β β' : TwoCell κ φ} →
              β ≅ᵗᶜ β' → β ⓣ-hor α ≅ᵗᶜ β' ⓣ-hor α
key-subst-eq (ⓣ-hor-congˡ {ρ = ρ} e) = ⊚-congʳ (lock-fmap-cong ρ (key-subst-eq e))

ⓣ-hor-congʳ : {μ ρ : DRA C D} {κ φ : DRA D E} {α α' : TwoCell μ ρ} {β : TwoCell κ φ} →
              α ≅ᵗᶜ α' → β ⓣ-hor α ≅ᵗᶜ β ⓣ-hor α'
key-subst-eq (ⓣ-hor-congʳ e) = ⊚-congˡ (key-subst-eq e)

ⓣ-hor-id : {μ : DRA C D} {ρ : DRA D E} → id-cell {μ = ρ} ⓣ-hor id-cell {μ = μ} ≅ᵗᶜ id-cell
key-subst-eq (ⓣ-hor-id {μ = μ}) = transˢ (id-subst-unitˡ _) (lock-fmap-id μ)

2-cell-interchange : {μ μ' μ'' : DRA D E} {ρ ρ' ρ'' : DRA C D}
                     {α : TwoCell μ μ'} {β : TwoCell μ' μ''} {γ : TwoCell ρ ρ'} {δ : TwoCell ρ' ρ''} →
                     (β ⓣ-vert α) ⓣ-hor (δ ⓣ-vert γ) ≅ᵗᶜ (β ⓣ-hor δ) ⓣ-vert (α ⓣ-hor γ)
key-subst-eq (2-cell-interchange {ρ'' = ρ''} {δ = δ}) =
  transˢ (⊚-congʳ (lock-fmap-⊚ ρ'' _ _)) (
    transˢ ⊚-assoc (
  transˢ (⊚-congʳ (transˢ (symˢ ⊚-assoc) (⊚-congˡ (naturality (transf δ) _)))) (
    transˢ (⊚-congʳ ⊚-assoc) (symˢ ⊚-assoc))))

-- In order to express that ⓣ-hor is associative and that id-cell is a
-- unit for ⓣ-hor, we need the associator and unitor in the 2-category
-- of base categories, DRAs and 2-cells. These proofs are therefore
-- included in Model.DRA.Equivalence.
