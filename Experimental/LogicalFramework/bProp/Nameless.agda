--------------------------------------------------
-- Instantiation of the general bProp defintion with the unit type ⊤ as type of names.
--   This essentially means that we have nameless bProps.
--------------------------------------------------

open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension

module Experimental.LogicalFramework.bProp.Nameless
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 ⊤ (erase-names-tmext _ _ 𝓉))
  where


open import Experimental.LogicalFramework.bProp.General ℳ 𝒯 ⊤ (erase-names-tmext _ _ 𝓉) 𝒷 public
