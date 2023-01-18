--------------------------------------------------
-- Interpretation of nameless formulas in the presheaf model over the
--   trivial base category
--------------------------------------------------

module Experimental.LogicalFramework.Formula.Interpretation.Nameless where

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.Modality as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Nameless
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.Nameless
open import Experimental.LogicalFramework.Formula.Nameless

private variable
  m : Mode
  Γ : Ctx m


⟦_⟧frm-nmls : Formula Γ → SemTy ⟦ Γ ⟧ctx-nmls
⟦ ⊤ᶠ ⟧frm-nmls = M.Unit'
⟦ ⊥ᶠ ⟧frm-nmls = M.Empty'
⟦ t1 ≡ᶠ t2 ⟧frm-nmls = M.Id ⟦ t1 ⟧tm-nmls ⟦ t2 ⟧tm-nmls
⟦ φ ⊃ ψ ⟧frm-nmls = ⟦ φ ⟧frm-nmls M.⇛ ⟦ ψ ⟧frm-nmls
⟦ φ ∧ ψ ⟧frm-nmls = ⟦ φ ⟧frm-nmls M.⊠ ⟦ ψ ⟧frm-nmls
⟦ ∀[ μ ∣ _ ∈ T ] φ ⟧frm-nmls = M.Pi ⟦ ⟨ μ ∣ T ⟩ ⟧ty ⟦ φ ⟧frm-nmls
⟦ ⟨ μ ∣ φ ⟩ ⟧frm-nmls = M.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧frm-nmls ⟩
