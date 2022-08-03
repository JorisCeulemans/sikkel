--------------------------------------------------
-- Instantiation of the general formula defintion with the unit type ⊤ as type of names.
--   This essentially means that we have nameless formulas.
--------------------------------------------------

module Experimental.LogicalFramework.Formula.Nameless where

open import Data.Unit


open import Experimental.LogicalFramework.Formula.General ⊤ public
