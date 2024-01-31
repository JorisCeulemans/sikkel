--------------------------------------------------
-- Module that re-exports all definitions involving predicates on MSTT programs
--------------------------------------------------

open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.bProp
  (ℬ : BiSikkelParameter)
  where

open BiSikkelParameter ℬ

open import Experimental.LogicalFramework.bProp.Named 𝒫 𝒷 public
open import Experimental.LogicalFramework.bProp.AlphaEquivalence 𝒫 𝒷 public
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧ public
