--------------------------------------------------
-- Definition of α-equivalence of bProps via a translation to nameless bProps
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.bProp.AlphaEquivalence (ℳ : ModeTheory) where

open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ

open import Experimental.LogicalFramework.bProp.Named ℳ
import Experimental.LogicalFramework.bProp.Nameless ℳ as NMLS
open import Experimental.LogicalFramework.MSTT.Syntax ℳ

private variable
  m : Mode
  Γ : Ctx m


erase-names-bprop : bProp Γ → NMLS.bProp (erase-names-ctx Γ)
erase-names-bprop ⊤ᶠ = NMLS.⊤ᶠ
erase-names-bprop ⊥ᶠ = NMLS.⊥ᶠ
erase-names-bprop (t1 ≡ᶠ t2) = erase-names-tm t1 NMLS.≡ᶠ erase-names-tm t2
erase-names-bprop (φ ⊃ ψ) = erase-names-bprop φ NMLS.⊃ erase-names-bprop ψ
erase-names-bprop (φ ∧ ψ) = erase-names-bprop φ NMLS.∧ erase-names-bprop ψ
erase-names-bprop (∀[ μ ∣ x ∈ T ] φ) = NMLS.∀[ μ ∣ _ ∈ T ] erase-names-bprop φ
erase-names-bprop ⟨ μ ∣ φ ⟩ = NMLS.⟨ μ ∣ erase-names-bprop φ ⟩

_≈αᶠ_ : (φ ψ : bProp Γ) → Set
φ ≈αᶠ ψ = erase-names-bprop φ ≡ erase-names-bprop ψ
