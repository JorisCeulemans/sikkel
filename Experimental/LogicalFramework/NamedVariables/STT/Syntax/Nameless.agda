--------------------------------------------------
-- Instantiation of the general STT syntax with the unit type ⊤ as type of names.
--   This essentially means that we have a nameless syntax.
--------------------------------------------------

module Experimental.LogicalFramework.NamedVariables.STT.Syntax.Nameless where

open import Data.Unit


open import Experimental.LogicalFramework.NamedVariables.STT.Syntax.Types public
open import Experimental.LogicalFramework.NamedVariables.STT.Syntax.General ⊤ public
