open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework
  (ℬ : BiSikkelParameter)
  where


open BiSikkelParameter ℬ


open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧ public
open import Experimental.LogicalFramework.Proof ℬ public
open import Experimental.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧ public
