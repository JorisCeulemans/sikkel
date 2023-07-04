--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT (but not interpreting it in a model)
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Data.String using (String)

module Experimental.LogicalFramework.MSTT.Syntax
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯 String)
  where

open import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ 𝒯 𝓉 public
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.Context ℳ 𝒯 public
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence ℳ 𝒯 𝓉 public
