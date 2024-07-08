--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT (𝒫 : MSTT-Parameter) where

open MSTT-Parameter

open import Experimental.LogicalFramework.MSTT.Syntax (𝒫 .ℳ) (𝒫 .𝒯) (𝒫 .𝓉) public hiding (_,,_∣_)
  -- ^ hiding _,,_∣_ (constructor for nameless telescopes) to avoid
  --   parsing issues
open import Experimental.LogicalFramework.MSTT.Interpretation (𝒫 .ℳ) (𝒫 .𝒯) (𝒫 .𝓉) (𝒫 .⟦𝓉⟧) public
open import Experimental.LogicalFramework.MSTT.BasicPrograms (𝒫 .ℳ) (𝒫 .𝒯) (𝒫 .𝓉) public
open import Experimental.LogicalFramework.MSTT.Normalization 𝒫 public
open import Experimental.LogicalFramework.MSTT.Extraction 𝒫 public
