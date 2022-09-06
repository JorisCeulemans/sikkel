--------------------------------------------------
-- Instantiation of the general MSTT syntax with the unit type ⊤ as type of names.
--   This essentially means that we have a nameless syntax.
--------------------------------------------------

module Experimental.LogicalFramework.MSTT.Syntax.Nameless where

open import Data.Unit


open import Experimental.LogicalFramework.MSTT.Syntax.Types public
open import Experimental.LogicalFramework.MSTT.Syntax.General ⊤ public
