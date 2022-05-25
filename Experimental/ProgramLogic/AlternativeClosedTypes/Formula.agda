--------------------------------------------------
-- Definition of formulas encoding logical propositions
--------------------------------------------------

module Experimental.ProgramLogic.AlternativeClosedTypes.Formula where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M using (Ctx; Ty; Tm; _≅ᵗʸ_)
import Model.CwF-Structure.Reflection.SubstitutionSequence as M
import Model.Type.Function as M
import Model.Type.Product as M
import Experimental.DependentTypes.Model.Function as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.ClosedTypes
open import Experimental.ClosedTypes.Pi
open import Experimental.ProgramLogic.AlternativeClosedTypes.STT

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
⟦ ∀[ T ] φ ⟧frm = sPi ⟦ T ⟧ty ⟦ φ ⟧frm

-- Applying a substitution to a formula.
_[_]frm : Formula Γ → SubstExpr Δ Γ → Formula Δ
(t1 ≡ᶠ t2) [ σ ]frm = (t1 [ σ ]tm) ≡ᶠ (t2 [ σ ]tm)
(φ ⊃ ψ) [ σ ]frm = (φ [ σ ]frm) ⊃ (ψ [ σ ]frm)
(φ ∧ ψ) [ σ ]frm = (φ [ σ ]frm) ∧ (ψ [ σ ]frm)
(∀[ T ] φ) [ σ ]frm = ∀[ T ] (φ [ σ ⊹ ]frm)

frm-subst-sound : (φ : Formula Γ) (σ : SubstExpr Δ Γ) → ⟦ φ ⟧frm M.[ ⟦ σ ⟧subst ] ≅ᵗʸ ⟦ φ [ σ ]frm ⟧frm
frm-subst-sound (t1 ≡ᶠ t2) σ =
  M.≅ᵗʸ-trans (M.Id-natural _) (M.Id-cong (closed-ty-natural _ _) (M.move-ι⁻¹-right (M.≅ᵗʸ-sym (closed-ty-natural _ _)) (tm-subst-sound t1 σ))
                                                                  (M.move-ι⁻¹-right (M.≅ᵗʸ-sym (closed-ty-natural _ _)) (tm-subst-sound t2 σ)))
frm-subst-sound (φ ⊃ ψ) σ = M.≅ᵗʸ-trans (M.⇛-natural _) (M.⇛-cong (frm-subst-sound φ σ) (frm-subst-sound ψ σ))
frm-subst-sound (φ ∧ ψ) σ = M.≅ᵗʸ-trans (M.⊠-natural _) (M.⊠-cong (frm-subst-sound φ σ) (frm-subst-sound ψ σ))
frm-subst-sound (∀[ T ] φ) σ = M.≅ᵗʸ-trans (sPi-natural _) (sPi-cong₂ (M.≅ᵗʸ-trans (M.ty-subst-cong-subst (⊹-sound σ) ⟦ φ ⟧frm)
                                                                                   (frm-subst-sound φ (σ ⊹))))
