--------------------------------------------------
-- Instantiation of the general definition of bProps with strings as names
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.bProp.Named (𝒫 : MSTT-Parameter) where

open import Data.String


open import Experimental.LogicalFramework.bProp.General 𝒫 String public
