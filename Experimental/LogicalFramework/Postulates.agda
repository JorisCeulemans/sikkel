-- This module lists all axioms that are currently postulated.
-- They should eventually be proved.

{-# OPTIONS --allow-unsolved-metas #-}

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
open import Data.String

module Experimental.LogicalFramework.Postulates
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.String using (String)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Model.Type.Function as M

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n


postulate
  v0-2lock-sound : (μ : Modality n o) (κ : Modality m n) (x : String) (Γ : Ctx o) (T : Ty m) →
                   ⟦ var' {Γ = Γ ,, μ ⓜ κ ∣ x ∈ T ,lock⟨ μ ⟩ ,lock⟨ κ ⟩} x {vlock (vlock (vzero id-cell))} ⟧tm
                     M.≅ᵗᵐ
                   dra-elim ⟦ κ ⟧mod (dra-elim ⟦ μ ⟧mod (
                     M.ι⁻¹[ eq-dra-ty-closed (⟦ⓜ⟧-sound μ κ) (ty-closed-natural T) ] (M.ξcl (ty-closed-natural ⟨ μ ⓜ κ ∣ T ⟩) {Γ = ⟦ Γ ⟧ctx})))
