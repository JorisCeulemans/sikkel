--------------------------------------------------
-- Instantiation of the general definition of bProps with strings as names
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.bProp.Named (ℳ : ModeTheory) where

open import Data.String


open import Experimental.LogicalFramework.bProp.General ℳ String public
