--------------------------------------------------
-- Extraction of proof contexts and evidence
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.Proof.Extraction
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.Unit
open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; tm-setoid to semtm-setoid) using ()

open import Experimental.LogicalFramework.MSTT 𝒫 hiding (refl)
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.Soundness 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n : Mode
  μ ρ : Modality m n
  Γ Δ : Ctx m
  T S : Ty m


--------------------------------------------------
-- Definition of extractability for proof contexts

-- Contrary to MSTT contexts and types and to bProps, we do not define
-- a proof context to be extractable when its denotation is isomorphic
-- to an Agda type. The main reason for this is that it is not evident
-- that an extractable proof context gives rise to an extractable
-- context by removing all bProp assumptions via to-ctx (and that is
-- needed to even state that extending an extractable proof context
-- with an extractable proposition yields an extractable result).
data ExtractableProofCtx : ProofCtx ★ → Set₁
to-ctx-extractable : {Ξ : ProofCtx ★} → ExtractableProofCtx Ξ → ExtractableCtx (to-ctx Ξ)

data ExtractableProofCtx where
  instance
    ◇-extr : ExtractableProofCtx ◇
    extend-var-extr : {Ξ : ProofCtx ★} → {{ExtractableProofCtx Ξ}} →
                      {x : Name} →
                      {T : Ty ★} → {{ExtractableTy T}} →
                      ExtractableProofCtx (Ξ ,,ᵛ 𝟙 ∣ x ∈ T)
    extend-prop-extr : {Ξ : ProofCtx ★} → {{exΞ : ExtractableProofCtx Ξ}} →
                       {x : Name} →
                       {φ : bProp (to-ctx Ξ ,lock⟨ 𝟙 ⟩)} →
                       {{ExtractableProp {{lock𝟙-extractable {{to-ctx-extractable exΞ}}}} φ}} →
                       ExtractableProofCtx (Ξ ,,ᵇ 𝟙 ∣ x ∈ φ)
    lock𝟙-pf-extr : {Ξ : ProofCtx ★} → {{ExtractableProofCtx Ξ}} →
                    ExtractableProofCtx (Ξ ,lock⟨ 𝟙 ⟩)

to-ctx-extractable ◇-extr = ◇-extractable
to-ctx-extractable (extend-var-extr {{exΞ}} {{exT}}) = ,,-extractable {{to-ctx-extractable exΞ}} {{exT}}
to-ctx-extractable (extend-prop-extr {{exΞ}}) = to-ctx-extractable exΞ
to-ctx-extractable (lock𝟙-pf-extr {{exΞ}}) = lock𝟙-extractable {{to-ctx-extractable exΞ}}


-- If a proof context Ξ is extractable, it gives rise to an Agda type
-- extract-ctx Ξ. This Agda type is intended to be isomorphic to the
-- proof context's denotatation ⟦ Ξ ⟧pctx M.⟨ tt ⟩, but actually we
-- only need one direction of this isomorphism to extract BiSikkel
-- proofs to Agda proofs.
extract-pfctx : (Ξ : ProofCtx ★) → {{ExtractableProofCtx Ξ}} → Set
pfctx-extract-to-denotation : (Ξ : ProofCtx ★) {{exΞ : ExtractableProofCtx Ξ}} →
                              extract-pfctx Ξ → ⟦ Ξ ⟧pctx M.⟨ tt ⟩

extract-pfctx .◇                 {{ ◇-extr }}                               = ⊤
extract-pfctx .(Ξ ,,ᵛ 𝟙 ∣ _ ∈ T) {{ extend-var-extr {Ξ} {_} {T} }}          = extract-pfctx Ξ × extract-ty T
extract-pfctx .(Ξ ,,ᵇ 𝟙 ∣ _ ∈ φ) {{ extend-prop-extr {Ξ} {{exΞ}} {_} {φ} }} =
  Σ[ aΞ ∈ extract-pfctx Ξ ]
    extract-bprop {{_}} φ (Inverse.to (extract-ctx-iso {{to-ctx-extractable exΞ}}) (
                            M.func (to-ctx-subst Ξ) (
                            pfctx-extract-to-denotation Ξ aΞ)))
extract-pfctx .(Ξ ,lock⟨ 𝟙 ⟩)    {{ lock𝟙-pf-extr {Ξ} }}                    = extract-pfctx Ξ

pfctx-extract-to-denotation .◇ {{ ◇-extr }} ξ = tt
pfctx-extract-to-denotation .(Ξ ,,ᵛ 𝟙 ∣ _ ∈ T) {{ extend-var-extr {Ξ} {{exΞ}} {_} {T} }} [ ξ , t ] =
  [ pfctx-extract-to-denotation Ξ ξ , Inverse.from (extract-ty-iso {T}) t ]
pfctx-extract-to-denotation .(Ξ ,,ᵇ 𝟙 ∣ _ ∈ φ) {{ extend-prop-extr {Ξ} {{exΞ}} {_} {φ} }} [ ξ , f ] =
  [ pfctx-extract-to-denotation Ξ ξ
  , M.ty-ctx-subst ⟦ φ ⟧bprop (Inverse.strictlyInverseʳ (extract-ctx-iso {{ to-ctx-extractable exΞ }}) _)
                              (Inverse.from (extract-prop-iso {{_}} {φ} _) f)
  ]
pfctx-extract-to-denotation .(Ξ ,lock⟨ 𝟙 ⟩) {{ lock𝟙-pf-extr {Ξ} {{exΞ}} }} ξ = pfctx-extract-to-denotation Ξ ξ


extract-pfctx-to-ctx : {Ξ : ProofCtx ★} {{exΞ : ExtractableProofCtx Ξ}} →
                       extract-pfctx Ξ → extract-ctx (to-ctx Ξ) {{to-ctx-extractable exΞ}}
extract-pfctx-to-ctx {Ξ} {{exΞ}} =
  Inverse.to (extract-ctx-iso {{to-ctx-extractable exΞ}})
  ∘ M.func (to-ctx-subst Ξ)
  ∘ pfctx-extract-to-denotation Ξ


--------------------------------------------------
-- Extraction of evidence (i.e. semantic terms) of a bProp φ in a
-- proof context Ξ to a dependent Agda function.

module ExtractProof
  {Ξ : ProofCtx ★} {{exΞ : ExtractableProofCtx Ξ}}
  {φ : bProp (to-ctx Ξ)} {{exφ : ExtractableProp {{to-ctx-extractable exΞ}} φ}}
  where

  extract-evidence : Evidence Ξ φ →
                     (ξ : extract-pfctx Ξ) →
                     extract-bprop {{to-ctx-extractable exΞ}} φ (extract-pfctx-to-ctx {Ξ} ξ)
  extract-evidence ev ξ =
    Inverse.to (extract-prop-iso {{_}} {φ} (extract-pfctx-to-ctx {Ξ} ξ)) (
      M.ty-ctx-subst ⟦ φ ⟧bprop (sym (Inverse.strictlyInverseʳ (extract-ctx-iso {{to-ctx-extractable exΞ}}) _)) (
      ev M.⟨ tt , pfctx-extract-to-denotation Ξ ξ ⟩'))
