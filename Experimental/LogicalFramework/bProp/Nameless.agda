--------------------------------------------------
-- Instantiation of the general bProp defintion with the unit type ⊤ as type of names.
--   This essentially means that we have nameless bProps.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.bProp.Nameless (𝒫 : MSTT-Parameter) where

open import Data.Unit


open import Experimental.LogicalFramework.bProp.General 𝒫 ⊤ public
