open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof
  (ℬ : BiSikkelParameter)
  where

open BiSikkelParameter ℬ

open import Experimental.LogicalFramework.Proof.CheckingMonad public
open import Experimental.LogicalFramework.Proof.Definition ℬ public
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧ public
open import Experimental.LogicalFramework.Proof.Checker ℬ public
