--------------------------------------------------
-- Definition of formulas and their substitution
--   Just as STT syntax, the general definition of formulas is
--   parametrised by a type of names to represent variables. It is not
--   recommended to directly import this module, but rather use
--   Formula.Named.
--------------------------------------------------

module Experimental.LogicalFramework.Formula.General (Name : Set) where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.STT.Syntax.Types
open import Experimental.LogicalFramework.STT.Syntax.General Name

private variable
  Γ Δ : CtxExpr


infixl 3 ∀[_∈_]_
infixr 6 _⊃_
infixl 9 _∧_
infix 12 _≡ᶠ_
data Formula (Γ : CtxExpr) : Set where
  ⊤ᶠ ⊥ᶠ : Formula Γ
  _≡ᶠ_ : {T : TyExpr} (t1 t2 : TmExpr Γ T) → Formula Γ
  _⊃_ _∧_ : (φ ψ : Formula Γ) → Formula Γ
  ∀[_∈_]_ : (x : Name) (T : TyExpr) → Formula (Γ ,, x ∈ T) → Formula Γ

¬ : Formula Γ → Formula Γ
¬ φ = φ ⊃ ⊥ᶠ

-- Applying a substitution to a formula.
_[_]frm : Formula Γ → SubstExpr Δ Γ → Formula Δ
⊤ᶠ [ σ ]frm = ⊤ᶠ
⊥ᶠ [ σ ]frm = ⊥ᶠ
(t1 ≡ᶠ t2) [ σ ]frm = (t1 [ σ ]tm) ≡ᶠ (t2 [ σ ]tm)
(φ ⊃ ψ) [ σ ]frm = (φ [ σ ]frm) ⊃ (ψ [ σ ]frm)
(φ ∧ ψ) [ σ ]frm = (φ [ σ ]frm) ∧ (ψ [ σ ]frm)
(∀[ x ∈ T ] φ) [ σ ]frm = ∀[ x ∈ T ] (φ [ σ ⊹⟨ x ⟩ ]frm)
