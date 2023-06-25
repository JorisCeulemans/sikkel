--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT (𝒫 : MSTT-Parameter) where

open MSTT-Parameter

open import Experimental.LogicalFramework.MSTT.Syntax (𝒫 .ℳ) (𝒫 .𝒯) public
open import Experimental.LogicalFramework.MSTT.Interpretation (𝒫 .ℳ) (𝒫 .𝒯) public
