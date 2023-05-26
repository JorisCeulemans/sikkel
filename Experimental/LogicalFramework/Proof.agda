open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.Proof
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Experimental.LogicalFramework.Proof.CheckingMonad public
open import Experimental.LogicalFramework.Proof.Definition ℳ public
open import Experimental.LogicalFramework.Proof.Context ℳ ⟦ℳ⟧ public
open import Experimental.LogicalFramework.Proof.Checker ℳ ⟦ℳ⟧ public
