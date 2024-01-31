open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof
  (ℬ : BiSikkelParameter)
  where

open import Experimental.LogicalFramework.Proof.CheckingMonad public
open import Experimental.LogicalFramework.Proof.Definition ℬ public
open import Experimental.LogicalFramework.Proof.Context ℬ public
open import Experimental.LogicalFramework.Proof.Checker ℬ public
