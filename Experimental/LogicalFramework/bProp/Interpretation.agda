--------------------------------------------------
-- Interpretation of propositions in the presheaf model over the trivial
--   base category
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.bProp.Interpretation
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
open import Experimental.LogicalFramework.bProp.Named ℳ
open import Experimental.LogicalFramework.bProp.AlphaEquivalence ℳ
open import Experimental.LogicalFramework.bProp.Interpretation.Nameless ℳ ⟦ℳ⟧

private variable
  m : Mode
  Γ Δ : Ctx m


-- Just as with the STT interpretation, this interpretation goes via unnamed propositions.
--   This makes it nearly trivial to prove that α-equivalent propositions have the same
--   interpretation.
⟦_⟧bprop : bProp Γ → SemTy ⟦ Γ ⟧ctx
⟦ φ ⟧bprop = ⟦ erase-names-bprop φ ⟧bprop-nmls

{-
bprop-subst-sound : (φ : bProp Γ) (σ : SubstExpr Δ Γ) → ⟦ φ ⟧bprop M.[ ⟦ σ ⟧subst ] ≅ᵗʸ ⟦ φ [ σ ]bprop ⟧bprop
bprop-subst-sound ⊤ᵇ σ = M.Const-natural _ _
bprop-subst-sound ⊥ᵇ σ = M.Const-natural _ _
bprop-subst-sound (t1 ≡ᵇ t2) σ =
  M.transᵗʸ (M.Id-natural _) (M.Id-cong (closed-ty-natural _ _) (M.move-ι⁻¹-right (M.symᵗʸ (closed-ty-natural _ _)) (tm-subst-sound t1 σ))
                                                                  (M.move-ι⁻¹-right (M.symᵗʸ (closed-ty-natural _ _)) (tm-subst-sound t2 σ)))
bprop-subst-sound (φ ⊃ ψ) σ = M.transᵗʸ (M.⇛-natural _) (M.⇛-cong (bprop-subst-sound φ σ) (bprop-subst-sound ψ σ))
bprop-subst-sound (φ ∧ ψ) σ = M.transᵗʸ (M.⊠-natural _) (M.⊠-cong (bprop-subst-sound φ σ) (bprop-subst-sound ψ σ))
bprop-subst-sound (∀[ x ∈ T ] φ) σ = M.transᵗʸ (sPi-natural _) (sPi-cong₂ (bprop-subst-sound φ (σ ⊹⟨ x ⟩)))
-}
