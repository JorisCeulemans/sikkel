--------------------------------------------------
-- Definition of the mode theory for guarded recursive type theory
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.ModeTheory where

open import Model.Modality using (reflᵐ)

open import MSTT.Parameter.ModeTheory

open import Applications.GuardedRecursion.MSTT.ModeTheory.TwoCells

-- Re-exporting the expressions and equality tests of the mode theory.
open import Applications.GuardedRecursion.MSTT.ModeTheory.Expressions public
open import Applications.GuardedRecursion.MSTT.ModeTheory.Equivalence public using (_≟mode_; _≃ᵐ?_)

GR-mode-theory : ModeTheory
ModeTheory.ModeExpr GR-mode-theory = ModeExpr
ModeTheory.show-mode GR-mode-theory = show-mode
ModeTheory.⟦_⟧mode GR-mode-theory = ⟦_⟧mode
ModeTheory._≟mode_ GR-mode-theory = _≟mode_
ModeTheory.ModalityExpr GR-mode-theory = ModalityExpr
ModeTheory.𝟙 GR-mode-theory = 𝟙
ModeTheory._ⓜ_ GR-mode-theory = _ⓜ_
ModeTheory.show-modality GR-mode-theory = show-modality
ModeTheory.⟦_⟧modality GR-mode-theory = ⟦_⟧modality
ModeTheory.𝟙-interpretation GR-mode-theory = reflᵐ
ModeTheory.ⓜ-interpretation GR-mode-theory = λ _ _ → reflᵐ
ModeTheory._≃ᵐ?_ GR-mode-theory = _≃ᵐ?_
ModeTheory.TwoCellExpr GR-mode-theory = TwoCellExpr
ModeTheory.id-cell GR-mode-theory = id-cell
ModeTheory.⟦_∈_⇒_⟧two-cell GR-mode-theory = check-two-cell
