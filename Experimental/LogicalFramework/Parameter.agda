module Experimental.LogicalFramework.Parameter where

open import Data.String

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
open import Experimental.LogicalFramework.Parameter.ProofExtension

open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension
open import Experimental.LogicalFramework.bProp.AlphaEquivalence.bPropExtension


record BiSikkelParameter : Set₁ where
  field
    𝒫 : MSTT-Parameter

  open MSTT-Parameter 𝒫 public

  field
    𝒷 : bPropExt ℳ 𝒯 String 𝓉
    ⟦𝒷⟧ : bPropExtSem ℳ 𝒯 (erase-names-tmext ℳ 𝒯 𝓉) (erase-names-bpext 𝒫 𝒷)
    𝓅 : ProofExt 𝒫 𝒷
