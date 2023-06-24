--------------------------------------------------
-- Module that re-exports all definitions involving predicates on STT programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics

module Experimental.LogicalFramework.bProp
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheorySemantics ℳ)
  where


open import Experimental.LogicalFramework.bProp.Named ℳ public
open import Experimental.LogicalFramework.bProp.AlphaEquivalence ℳ public
open import Experimental.LogicalFramework.bProp.Interpretation ℳ ⟦ℳ⟧ public
