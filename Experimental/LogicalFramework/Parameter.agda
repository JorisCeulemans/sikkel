module Experimental.LogicalFramework.Parameter where

open import Data.String

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
open import Experimental.LogicalFramework.Parameter.ProofExtension


record BiSikkelParameter : Set₁ where
  no-eta-equality
  field
    𝒫 : MSTT-Parameter

  open MSTT-Parameter 𝒫 public

  field
    𝒷 : bPropExt ℳ 𝒯 𝓉
    ⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷
    𝓅 : ProofExt 𝒫 𝒷 ⟦𝒷⟧
