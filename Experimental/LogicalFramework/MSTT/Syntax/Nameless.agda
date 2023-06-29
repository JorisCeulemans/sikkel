--------------------------------------------------
-- Instantiation of the general MSTT syntax with the unit type ⊤ as type of names.
--   This essentially means that we have a nameless syntax.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax.Nameless
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.Unit


open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯 public
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 ⊤ public
open import Experimental.LogicalFramework.MSTT.Syntax.General ℳ 𝒯 ⊤ public
