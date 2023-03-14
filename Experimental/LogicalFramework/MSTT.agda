--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.MSTT (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ) where

open import Experimental.LogicalFramework.MSTT.Syntax ℳ public
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ ⟦ℳ⟧ public
