--------------------------------------------------
-- Module that re-exports all definitions involving predicates on STT programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.bProp
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where


open import Experimental.LogicalFramework.bProp.Named ℳ public
open import Experimental.LogicalFramework.bProp.AlphaEquivalence ℳ public
open import Experimental.LogicalFramework.bProp.Interpretation ℳ ⟦ℳ⟧ public
