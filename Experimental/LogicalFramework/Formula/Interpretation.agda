--------------------------------------------------
-- Interpretation of formulas in the presheaf model over the trivial
--   base category
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.Formula.Interpretation
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy) using (_≅ᵗʸ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open ModeTheory ℳ
open ModeTheoryInterpretation ⟦ℳ⟧

open import Experimental.LogicalFramework.MSTT ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.Formula.Named ℳ
open import Experimental.LogicalFramework.Formula.AlphaEquivalence ℳ
open import Experimental.LogicalFramework.Formula.Interpretation.Nameless ℳ ⟦ℳ⟧

private variable
  m : Mode
  Γ Δ : Ctx m


-- Just as with the STT interpretation, this interpretation goes via unnamed formulas.
--   This makes it nearly trivial to prove that α-equivalent formulas have the same
--   interpretation.
⟦_⟧frm : Formula Γ → SemTy ⟦ Γ ⟧ctx
⟦ φ ⟧frm = ⟦ erase-names-frm φ ⟧frm-nmls

{-
frm-subst-sound : (φ : Formula Γ) (σ : SubstExpr Δ Γ) → ⟦ φ ⟧frm M.[ ⟦ σ ⟧subst ] ≅ᵗʸ ⟦ φ [ σ ]frm ⟧frm
frm-subst-sound ⊤ᶠ σ = M.Const-natural _ _
frm-subst-sound ⊥ᶠ σ = M.Const-natural _ _
frm-subst-sound (t1 ≡ᶠ t2) σ =
  M.transᵗʸ (M.Id-natural _) (M.Id-cong (closed-ty-natural _ _) (M.move-ι⁻¹-right (M.symᵗʸ (closed-ty-natural _ _)) (tm-subst-sound t1 σ))
                                                                  (M.move-ι⁻¹-right (M.symᵗʸ (closed-ty-natural _ _)) (tm-subst-sound t2 σ)))
frm-subst-sound (φ ⊃ ψ) σ = M.transᵗʸ (M.⇛-natural _) (M.⇛-cong (frm-subst-sound φ σ) (frm-subst-sound ψ σ))
frm-subst-sound (φ ∧ ψ) σ = M.transᵗʸ (M.⊠-natural _) (M.⊠-cong (frm-subst-sound φ σ) (frm-subst-sound ψ σ))
frm-subst-sound (∀[ x ∈ T ] φ) σ = M.transᵗʸ (sPi-natural _) (sPi-cong₂ (frm-subst-sound φ (σ ⊹⟨ x ⟩)))
-}
