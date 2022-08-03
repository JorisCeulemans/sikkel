--------------------------------------------------
-- Interpretation of formulas in the presheaf model over the trivial
--   base category
--------------------------------------------------

module Experimental.LogicalFramework.Formula.Interpretation where

open import Model.CwF-Structure as M using (Ctx; Ty; Tm; _≅ᵗʸ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.ClosedTypes
open import Experimental.ClosedTypes.Pi

open import Experimental.LogicalFramework.STT
open import Experimental.LogicalFramework.Formula.Named
open import Experimental.LogicalFramework.Formula.AlphaEquivalence
open import Experimental.LogicalFramework.Formula.Interpretation.Nameless

private variable
  Γ Δ : CtxExpr


-- Just as with the STT interpretation, this interpretation goes via unnamed formulas.
--   This makes it nearly trivial to prove that α-equivalent formulas have the same
--   interpretation.
⟦_⟧frm : Formula Γ → Ty ⟦ Γ ⟧ctx
⟦ φ ⟧frm = ⟦ erase-names-frm φ ⟧frm-nmls

frm-subst-sound : (φ : Formula Γ) (σ : SubstExpr Δ Γ) → ⟦ φ ⟧frm M.[ ⟦ σ ⟧subst ] ≅ᵗʸ ⟦ φ [ σ ]frm ⟧frm
frm-subst-sound (t1 ≡ᶠ t2) σ =
  M.≅ᵗʸ-trans (M.Id-natural _) (M.Id-cong (closed-ty-natural _ _) (M.move-ι⁻¹-right (M.≅ᵗʸ-sym (closed-ty-natural _ _)) (tm-subst-sound t1 σ))
                                                                  (M.move-ι⁻¹-right (M.≅ᵗʸ-sym (closed-ty-natural _ _)) (tm-subst-sound t2 σ)))
frm-subst-sound (φ ⊃ ψ) σ = M.≅ᵗʸ-trans (M.⇛-natural _) (M.⇛-cong (frm-subst-sound φ σ) (frm-subst-sound ψ σ))
frm-subst-sound (φ ∧ ψ) σ = M.≅ᵗʸ-trans (M.⊠-natural _) (M.⊠-cong (frm-subst-sound φ σ) (frm-subst-sound ψ σ))
frm-subst-sound (∀[ x ∈ T ] φ) σ = M.≅ᵗʸ-trans (sPi-natural _) (sPi-cong₂ (frm-subst-sound φ (σ ⊹⟨ x ⟩)))
