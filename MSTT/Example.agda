--------------------------------------------------
-- Example program in MSTT
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension
open import MSTT.Parameter.TermExtension

module MSTT.Example (mt : ModeTheory) (ty-ext : TyExt mt) (tm-ext : TmExt mt ty-ext) where

open ModeTheory mt

open import MSTT.Syntax.Type mt ty-ext
open import MSTT.Syntax.Term mt ty-ext tm-ext

private variable
  m n : ModeExpr


-- The following is an implementation of the applicative operator for
-- modalities, as shown in the CPP submission.

_⊛⟨_⟩_ : TmExpr n → ModalityExpr m n → TmExpr n → TmExpr n
f ⊛⟨ μ ⟩ t = mod-intro μ (mod-elim μ f ∙ mod-elim μ t)
