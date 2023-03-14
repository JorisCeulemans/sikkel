--------------------------------------------------
-- Instantiation of the general formula defintion with the unit type ⊤ as type of names.
--   This essentially means that we have nameless formulas.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.Formula.Nameless (ℳ : ModeTheory) where

open import Data.Unit


open import Experimental.LogicalFramework.Formula.General ℳ ⊤ public
