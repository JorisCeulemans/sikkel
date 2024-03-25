--------------------------------------------------
-- Module that re-exports all definitions involving predicates on MSTT programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.bProp
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷 public
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧ public
