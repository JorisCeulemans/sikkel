--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT (but not interpreting it in a model)
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ 𝒯 public
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence ℳ 𝒯 public
