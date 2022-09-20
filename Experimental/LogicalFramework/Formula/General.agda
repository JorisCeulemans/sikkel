--------------------------------------------------
-- Definition of formulas and their substitution
--   Just as MSTT syntax, the general definition of formulas is
--   parametrised by a type of names to represent variables. It is not
--   recommended to directly import this module, but rather use
--   Formula.Named.
--------------------------------------------------

module Experimental.LogicalFramework.Formula.General (Name : Set) where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Types
open import Experimental.LogicalFramework.MSTT.Syntax.General Name

private variable
  m n : Mode
  μ ρ : Modality m n
  x : Name
  Γ Δ : Ctx m
  T : Ty m


infixl 3 ∀[_∣_∈_]_
infixr 6 _⊃_
infixl 9 _∧_
infix 12 _≡ᶠ_

-- TODO: include connective for disjunction and existential quantification.
data Formula (Γ : Ctx m) : Set where
  ⊤ᶠ ⊥ᶠ : Formula Γ
  _≡ᶠ_ : {T : Ty m} (t1 t2 : Tm Γ T) → Formula Γ
  _⊃_ _∧_ : (φ ψ : Formula Γ) → Formula Γ
  ∀[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → Formula (Γ ,, μ ∣ x ∈ T) → Formula Γ
  ⟨_∣_⟩ : (μ : Modality n m) → Formula (Γ ,lock⟨ μ ⟩) → Formula Γ

¬ : Formula Γ → Formula Γ
¬ φ = φ ⊃ ⊥ᶠ


-- A formula can be traversed whenever terms can be traversed
record FrmTravStruct (Trav : ∀ {m} → Ctx m → Ctx m → Set) : Set where
  field
    trav-tm : Tm Δ T → Trav Γ Δ → Tm Γ T
    lift : Trav Γ Δ → Trav (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
    lock : Trav Γ Δ → Trav (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)

  traverse-frm : Formula Δ → Trav Γ Δ → Formula Γ
  traverse-frm ⊤ᶠ σ = ⊤ᶠ
  traverse-frm ⊥ᶠ σ = ⊥ᶠ
  traverse-frm (t1 ≡ᶠ t2) σ = trav-tm t1 σ ≡ᶠ trav-tm t2 σ
  traverse-frm (φ ⊃ ψ) σ = traverse-frm φ σ ⊃ traverse-frm ψ σ
  traverse-frm (φ ∧ ψ) σ = traverse-frm φ σ ∧ traverse-frm ψ σ
  traverse-frm (∀[ μ ∣ x ∈ T ] φ) σ = ∀[ μ ∣ x ∈ T ] traverse-frm φ (lift σ)
  traverse-frm ⟨ μ ∣ φ ⟩ σ = ⟨ μ ∣ traverse-frm φ (lock σ) ⟩

open FrmTravStruct using (traverse-frm)


renFrmTrav : FrmTravStruct Ren
FrmTravStruct.trav-tm renFrmTrav = rename-tm
FrmTravStruct.lift renFrmTrav = lift-ren
FrmTravStruct.lock renFrmTrav = λ σ → σ ,rlock⟨ _ ⟩

rename-frm : Formula Δ → Ren Γ Δ → Formula Γ
rename-frm = traverse-frm renFrmTrav


subFrmTrav : FrmTravStruct Sub
FrmTravStruct.trav-tm subFrmTrav = _[_]tm
FrmTravStruct.lift subFrmTrav = lift-sub
FrmTravStruct.lock subFrmTrav = λ σ → σ ,slock⟨ _ ⟩

_[_]frm : Formula Δ → Sub Γ Δ → Formula Γ
φ [ σ ]frm = traverse-frm subFrmTrav φ σ


-- Isomorphisms witnessing the functoriality of locks (wrt formulas)
lock𝟙-frm : Formula Γ → Formula (Γ ,lock⟨ 𝟙 ⟩)
lock𝟙-frm t = rename-frm t (lock𝟙-ren)

unlock𝟙-frm : Formula (Γ ,lock⟨ 𝟙 ⟩) → Formula Γ
unlock𝟙-frm t = rename-frm t (unlock𝟙-ren)

fuselocks-frm : Formula (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) → Formula (Γ ,lock⟨ μ ⓜ ρ ⟩)
fuselocks-frm t = rename-frm t fuselocks-ren

unfuselocks-frm : Formula (Γ ,lock⟨ μ ⓜ ρ ⟩) → Formula (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)
unfuselocks-frm t = rename-frm t unfuselocks-ren
