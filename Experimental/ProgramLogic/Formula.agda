--------------------------------------------------
-- Definition of formulas encoding logical propositions
--------------------------------------------------

module Experimental.ProgramLogic.Formula where

open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
import Model.Type.Function as M
import Model.Type.Product as M
import Experimental.DependentTypes.Model.Function as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.ProgramLogic.STT

private variable
  Γ Δ : CtxExpr



data Formula (Γ : CtxExpr) : Set where
  _≡ᶠ_ : {T : TyExpr} (t1 t2 : TmExpr Γ T) → Formula Γ
  _⊃_ _∧_ : (φ ψ : Formula Γ) → Formula Γ
  ∀[_]_ : (T : TyExpr) → Formula (Γ ,, T) → Formula Γ

-- A formula can be interpreted as a (dependent) type in the presheaf
--   model over base category ★.
⟦_⟧frm : Formula Γ → Ty ⟦ Γ ⟧ctx
⟦ t1 ≡ᶠ t2 ⟧frm = M.Id ⟦ t1 ⟧tm ⟦ t2 ⟧tm
⟦ φ ⊃ ψ ⟧frm = ⟦ φ ⟧frm M.⇛ ⟦ ψ ⟧frm
⟦ φ ∧ ψ ⟧frm = ⟦ φ ⟧frm M.⊠ ⟦ ψ ⟧frm
⟦ ∀[ T ] φ ⟧frm = M.Pi ⟦ T ⟧ty ⟦ φ ⟧frm

-- Applying a substitution to a formula.
_[_]frm : Formula Γ → SubstExpr Δ Γ → Formula Δ
(t1 ≡ᶠ t2) [ σ ]frm = (t1 [ σ ]tm) ≡ᶠ (t2 [ σ ]tm)
(φ ⊃ ψ) [ σ ]frm = (φ [ σ ]frm) ⊃ (ψ [ σ ]frm)
(φ ∧ ψ) [ σ ]frm = (φ [ σ ]frm) ∧ (ψ [ σ ]frm)
(∀[ T ] φ) [ σ ]frm = ∀[ T ] (φ [ σ ⊹ ]frm)
