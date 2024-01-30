--------------------------------------------------
-- Instantiation of the general definition of bProps with strings as names
--------------------------------------------------

open import Data.String
open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension

module Experimental.LogicalFramework.bProp.Named
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 String 𝓉)
  where


open import Experimental.LogicalFramework.bProp.General ℳ 𝒯 String 𝓉 𝒷 public
