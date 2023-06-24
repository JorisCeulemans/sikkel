--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT (but not interpreting it in a model)
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

module Experimental.LogicalFramework.MSTT.Syntax (ℳ : ModeTheory) where

open import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ public
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence ℳ public
