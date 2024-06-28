open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.bProp.Extraction
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.Unit
open import Function
open import Function.Construct.Composition
open import Function.Construct.Identity
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; tm-setoid to semtm-setoid) using ()

open import Experimental.LogicalFramework.MSTT 𝒫 hiding (refl)
open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n : Mode
  μ ρ : Modality m n
  Γ Δ : Ctx m
  T S : Ty m



record ExtractableProp {Γ : Ctx ★} {{exΓ : ExtractableCtx Γ}} (φ : bProp Γ) : Set₁ where
  no-eta-equality
  field
    AgdaProp : extract-ctx Γ → Set
    extract-prop-iso : (γ : extract-ctx Γ) →
                       (⟦ φ ⟧bprop M.⟨ tt , Inverse.from (extract-ctx-iso {Γ}) γ ⟩) ↔ AgdaProp γ

  extract-prop-iso' : (γ : ⟦ Γ ⟧ctx M.⟨ tt ⟩) →
                      (⟦ φ ⟧bprop M.⟨ tt , γ ⟩) ↔ AgdaProp (Inverse.to (extract-ctx-iso {Γ}) γ)
  extract-prop-iso' γ =
    extract-prop-iso _
    ↔-∘
    M.ty-ctx-subst-iso ⟦ φ ⟧bprop (sym (Inverse.strictlyInverseʳ (extract-ctx-iso {Γ}) γ))

open ExtractableProp {{...}} public

extract-bprop : {Γ : Ctx ★} → {{_ : ExtractableCtx Γ}} →
                (φ : bProp Γ) → {{ExtractableProp φ}} →
                extract-ctx Γ → Set
extract-bprop φ = AgdaProp
