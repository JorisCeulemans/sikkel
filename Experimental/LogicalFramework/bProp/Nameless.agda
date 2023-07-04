--------------------------------------------------
-- Instantiation of the general bProp defintion with the unit type ⊤ as type of names.
--   This essentially means that we have nameless bProps.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.bProp.Nameless (𝒫 : MSTT-Parameter) where

open import Data.Unit

open MSTT-Parameter 𝒫
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension ℳ 𝒯


open import Experimental.LogicalFramework.bProp.General ℳ 𝒯 ⊤ (erase-names-tmext 𝓉) public
