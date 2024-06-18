open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics

module Experimental.LogicalFramework.MSTT.Normalization.ResultType
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.Nat

open ModeTheory ℳ
import Model.CwF-Structure as M
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ 𝒯 𝓉 ⟦𝓉⟧

private variable
  m : Mode
  T : Ty m
  Γ : Ctx m


Fuel : Set
Fuel = ℕ

record NormalizeResult (t : Tm Γ T) : Set where
  constructor normres
  field
    nt : Tm Γ T
    sound : ⟦ t ⟧tm M.≅ᵗᵐ ⟦ nt ⟧tm
