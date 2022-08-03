module Experimental.LogicalFramework.NamedVariables.Formula.Interpretation.Nameless where

open import Model.CwF-Structure as M using (Ctx; Ty; Tm; _≅ᵗʸ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.ClosedTypes
open import Experimental.ClosedTypes.Pi

open import Experimental.LogicalFramework.NamedVariables.STT.Syntax.Nameless
open import Experimental.LogicalFramework.NamedVariables.STT.Interpretation.Nameless
open import Experimental.LogicalFramework.NamedVariables.Formula.Nameless

private variable
  Γ Δ : CtxExpr


-- A formula can be interpreted as a (dependent) type in the presheaf
--   model over base category ★.
⟦_⟧frm-nmls : Formula Γ → Ty ⟦ Γ ⟧ctx-nmls
⟦ t1 ≡ᶠ t2 ⟧frm-nmls = M.Id ⟦ t1 ⟧tm-nmls ⟦ t2 ⟧tm-nmls
⟦ φ ⊃ ψ ⟧frm-nmls = ⟦ φ ⟧frm-nmls M.⇛ ⟦ ψ ⟧frm-nmls
⟦ φ ∧ ψ ⟧frm-nmls = ⟦ φ ⟧frm-nmls M.⊠ ⟦ ψ ⟧frm-nmls
⟦ ∀[ _ ∈ T ] φ ⟧frm-nmls = sPi ⟦ T ⟧ty ⟦ φ ⟧frm-nmls
