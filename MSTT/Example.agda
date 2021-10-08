--------------------------------------------------
-- Example program in MSTT
--------------------------------------------------

open import MSTT.ModeTheory
open import MSTT.TypeExtension

module MSTT.Example (mt : ModeTheory) (ty-ext : TyExt mt) where

open ModeTheory mt

open import MSTT.Syntax mt ty-ext

private variable
  m n : ModeExpr


-- The following is an implementation of the applicative operator for
-- modalities, as shown in the CPP submission.

_⊛⟨_⟩_ : TmExpr n → ModalityExpr m n → TmExpr n → TmExpr n
f ⊛⟨ μ ⟩ t = mod-intro μ (mod-elim μ f ∙ mod-elim μ t)
