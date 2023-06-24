open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics

module Experimental.LogicalFramework.Proof
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheorySemantics ℳ)
  where

open import Experimental.LogicalFramework.Proof.CheckingMonad public
open import Experimental.LogicalFramework.Proof.Definition ℳ public
open import Experimental.LogicalFramework.Proof.Context ℳ ⟦ℳ⟧ public
open import Experimental.LogicalFramework.Proof.Checker ℳ ⟦ℳ⟧ public
