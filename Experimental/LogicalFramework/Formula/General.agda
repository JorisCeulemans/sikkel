--------------------------------------------------
-- Definition of formulas and their substitution
--   Just as MSTT syntax, the general definition of formulas is
--   parametrised by a type of names to represent variables. It is not
--   recommended to directly import this module, but rather use
--   Formula.Named.
--------------------------------------------------

module Experimental.LogicalFramework.Formula.General (Name : Set) where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Types
open import Experimental.LogicalFramework.MSTT.Syntax.General Name

private variable
  m n : Mode
  Γ Δ : Ctx m


infixl 3 ∀[_∣_∈_]_
infixr 6 _⊃_
infixl 9 _∧_
infix 12 _≡ᶠ_
data Formula (Γ : Ctx m) : Set where
  _≡ᶠ_ : {T : Ty m} (t1 t2 : Tm Γ T) → Formula Γ
  _⊃_ _∧_ : (φ ψ : Formula Γ) → Formula Γ
  ∀[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → Formula (Γ ,, μ ∣ x ∈ T) → Formula Γ
  ⟨_∣_⟩ : (μ : Modality n m) → Formula (Γ ,lock⟨ μ ⟩) → Formula Γ

-- Applying a substitution to a formula.
_[_]frm : Formula Δ → Sub Γ Δ → Formula Γ
(t1 ≡ᶠ t2) [ σ ]frm = (t1 [ σ ]tm) ≡ᶠ (t2 [ σ ]tm)
(φ ⊃ ψ) [ σ ]frm = (φ [ σ ]frm) ⊃ (ψ [ σ ]frm)
(φ ∧ ψ) [ σ ]frm = (φ [ σ ]frm) ∧ (ψ [ σ ]frm)
(∀[ μ ∣ x ∈ T ] φ) [ σ ]frm = ∀[ μ ∣ x ∈ T ] (φ [ lift-sub σ ]frm)
⟨ μ ∣ φ ⟩ [ σ ]frm = ⟨ μ ∣ φ [ σ ,slock⟨ μ ⟩ ]frm ⟩
