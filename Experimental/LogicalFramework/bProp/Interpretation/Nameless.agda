--------------------------------------------------
-- Interpretation of nameless propositions in the presheaf model over the
--   trivial base category
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.bProp.Interpretation.Nameless
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.Modality as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

open ModeTheory ℳ
open ModeTheoryInterpretation ⟦ℳ⟧

open import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ
open import Experimental.LogicalFramework.MSTT.Interpretation.Nameless ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.bProp.Nameless ℳ

private variable
  m : Mode
  Γ : Ctx m


⟦_⟧bprop-nmls : bProp Γ → SemTy ⟦ Γ ⟧ctx-nmls
⟦ ⊤ᵇ ⟧bprop-nmls = M.Unit'
⟦ ⊥ᵇ ⟧bprop-nmls = M.Empty'
⟦ t1 ≡ᵇ t2 ⟧bprop-nmls = M.Id ⟦ t1 ⟧tm-nmls ⟦ t2 ⟧tm-nmls
⟦ ⟨ μ ∣ φ ⟩⊃ ψ ⟧bprop-nmls = M.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop-nmls ⟩ M.⇛ ⟦ ψ ⟧bprop-nmls
⟦ φ ∧ ψ ⟧bprop-nmls = ⟦ φ ⟧bprop-nmls M.⊠ ⟦ ψ ⟧bprop-nmls
⟦ ∀[ μ ∣ _ ∈ T ] φ ⟧bprop-nmls = M.Pi ⟦ ⟨ μ ∣ T ⟩ ⟧ty ⟦ φ ⟧bprop-nmls
⟦ ⟨ μ ∣ φ ⟩ ⟧bprop-nmls = M.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop-nmls ⟩
