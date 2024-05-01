--------------------------------------------------
-- Interpretation of propositions in a presheaf model
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics using (bPropExtSem)

module Experimental.LogicalFramework.bProp.Interpretation
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.List
open import Data.Product
open import Data.Unit.Polymorphic

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy) using (_≅ᵗʸ_)
import Model.DRA as DRA
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷
open Experimental.LogicalFramework.Parameter.bPropExtensionSemantics ℳ 𝒯 𝓉 hiding (bPropExtSem)

open bPropExtSem ⟦𝒷⟧

private variable
  m : Mode
  Γ Δ : Ctx m


⟦_⟧bprop : bProp Γ → SemTy ⟦ Γ ⟧ctx
⟦_⟧bpextargs : ∀ {arginfos} → ExtBPArgs arginfos Γ → SemProps arginfos Γ

⟦ ⊤ᵇ ⟧bprop = M.Unit'
⟦ ⊥ᵇ ⟧bprop = M.Empty'
⟦ t1 ≡ᵇ t2 ⟧bprop = M.Id ⟦ t1 ⟧tm ⟦ t2 ⟧tm
⟦ ⟨ μ ∣ φ ⟩⊃ ψ ⟧bprop = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop ⟩ M.⇛ ⟦ ψ ⟧bprop
⟦ φ ∧ ψ ⟧bprop = ⟦ φ ⟧bprop M.⊠ ⟦ ψ ⟧bprop
⟦ ∀[ μ ∣ _ ∈ T ] φ ⟧bprop = M.Pi ⟦ ⟨ μ ∣ T ⟩ ⟧ty ⟦ φ ⟧bprop
⟦ ⟨ μ ∣ φ ⟩ ⟧bprop = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop ⟩
⟦ ext c tmargs bpargs ⟧bprop = apply-sem-prop-constructor ⟦ c ⟧bp-code ⟦ tmargs ⟧tmextargs ⟦ bpargs ⟧bpextargs

⟦_⟧bpextargs {arginfos = []}    args         = tt
⟦_⟧bpextargs {arginfos = _ ∷ _} (arg , args) = ⟦ arg ⟧bprop , ⟦ args ⟧bpextargs
