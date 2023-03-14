--------------------------------------------------
-- Instantiation of the general definition of formulas with strings as names
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.Formula.Named (ℳ : ModeTheory) where

open import Data.String


open import Experimental.LogicalFramework.Formula.General ℳ String public
