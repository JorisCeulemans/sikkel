--------------------------------------------------
-- Definition of α-equivalence of bProps via a translation to nameless bProps
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.bProp.AlphaEquivalence (𝒫 : MSTT-Parameter) where

open import Relation.Binary.PropositionalEquality

open MSTT-Parameter 𝒫

open import Experimental.LogicalFramework.bProp.Named 𝒫
import Experimental.LogicalFramework.bProp.Nameless 𝒫 as NMLS
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉

private variable
  m : Mode
  Γ : Ctx m


erase-names-bprop : bProp Γ → NMLS.bProp (erase-names-ctx Γ)
erase-names-bprop ⊤ᵇ = NMLS.⊤ᵇ
erase-names-bprop ⊥ᵇ = NMLS.⊥ᵇ
erase-names-bprop (t1 ≡ᵇ t2) = erase-names-tm t1 NMLS.≡ᵇ erase-names-tm t2
erase-names-bprop (⟨ μ ∣ φ ⟩⊃ ψ) = NMLS.⟨ μ ∣ erase-names-bprop φ ⟩⊃ erase-names-bprop ψ
erase-names-bprop (φ ∧ ψ) = erase-names-bprop φ NMLS.∧ erase-names-bprop ψ
erase-names-bprop (∀[ μ ∣ x ∈ T ] φ) = NMLS.∀[ μ ∣ _ ∈ T ] erase-names-bprop φ
erase-names-bprop ⟨ μ ∣ φ ⟩ = NMLS.⟨ μ ∣ erase-names-bprop φ ⟩

_≈αᵇ_ : (φ ψ : bProp Γ) → Set
φ ≈αᵇ ψ = erase-names-bprop φ ≡ erase-names-bprop ψ
