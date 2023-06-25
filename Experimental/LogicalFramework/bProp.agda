--------------------------------------------------
-- Module that re-exports all definitions involving predicates on STT programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.bProp (𝒫 : MSTT-Parameter) where


open import Experimental.LogicalFramework.bProp.Named 𝒫 public
open import Experimental.LogicalFramework.bProp.AlphaEquivalence 𝒫 public
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 public
