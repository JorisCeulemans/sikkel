open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.Proof (𝒫 : MSTT-Parameter) where

open import Experimental.LogicalFramework.Proof.CheckingMonad public
open import Experimental.LogicalFramework.Proof.Definition 𝒫 public
open import Experimental.LogicalFramework.Proof.Context 𝒫 public
open import Experimental.LogicalFramework.Proof.Checker 𝒫 public
