--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT (but not interpreting it in a model)
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension

module Experimental.LogicalFramework.MSTT.Syntax
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯 public
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 public
open import Experimental.LogicalFramework.MSTT.Syntax.Terms ℳ 𝒯 𝓉 public
open import Experimental.LogicalFramework.MSTT.Syntax.Substitution ℳ 𝒯 𝓉 public
