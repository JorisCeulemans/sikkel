--------------------------------------------------
-- Module that re-exports all definitions involving predicates on STT programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

module Experimental.LogicalFramework.bProp (ℳ : ModeTheory) where


open import Experimental.LogicalFramework.bProp.Named ℳ public
open import Experimental.LogicalFramework.bProp.AlphaEquivalence ℳ public
open import Experimental.LogicalFramework.bProp.Interpretation ℳ public
