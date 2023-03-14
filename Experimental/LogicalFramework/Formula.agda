--------------------------------------------------
-- Module that re-exports all definitions involving predicates on STT programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.Formula
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where


open import Experimental.LogicalFramework.Formula.Named ℳ public
open import Experimental.LogicalFramework.Formula.AlphaEquivalence ℳ public
open import Experimental.LogicalFramework.Formula.Interpretation ℳ ⟦ℳ⟧ public
