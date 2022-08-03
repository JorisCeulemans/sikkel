module Experimental.LogicalFramework.NamedVariables.Formula.AlphaEquivalence where

open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.NamedVariables.Formula.Named
import Experimental.LogicalFramework.NamedVariables.Formula.Nameless as NMLS
open import Experimental.LogicalFramework.NamedVariables.STT

private variable
  Γ : CtxExpr


erase-names-frm : Formula Γ → NMLS.Formula (erase-names-ctx Γ)
erase-names-frm (t1 ≡ᶠ t2) = erase-names-tm t1 NMLS.≡ᶠ erase-names-tm t2
erase-names-frm (φ ⊃ ψ) = erase-names-frm φ NMLS.⊃ erase-names-frm ψ
erase-names-frm (φ ∧ ψ) = erase-names-frm φ NMLS.∧ erase-names-frm ψ
erase-names-frm (∀[ x ∈ T ] φ) = NMLS.∀[ _ ∈ T ] erase-names-frm φ

_≈αᶠ_ : (φ ψ : Formula Γ) → Set
φ ≈αᶠ ψ = erase-names-frm φ ≡ erase-names-frm ψ
