--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics

module Experimental.LogicalFramework.MSTT (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheorySemantics ℳ) where

open import Experimental.LogicalFramework.MSTT.Syntax ℳ public
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ ⟦ℳ⟧ public
