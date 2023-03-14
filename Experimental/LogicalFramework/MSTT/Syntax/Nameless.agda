--------------------------------------------------
-- Instantiation of the general MSTT syntax with the unit type ⊤ as type of names.
--   This essentially means that we have a nameless syntax.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.MSTT.Syntax.Nameless (ℳ : ModeTheory) where

open import Data.Unit


open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ public
open import Experimental.LogicalFramework.MSTT.Syntax.General ℳ ⊤ public
