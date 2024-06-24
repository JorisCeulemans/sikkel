open import Data.String
open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.Parameter.ProofExtension
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯
open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧

private variable
  m : Mode


ProofCheckExt : (infos : List (ArgInfo m)) (pfarg-names : ArgBoundNames infos)
                (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) →
                Set
ProofCheckExt []             pfarg-names                  Ξ φ = PCM (PCResult Ξ φ)
ProofCheckExt (info ∷ infos) (pfarg-names , pfargs-names) Ξ φ =
  ((Ξ' : ProofCtx (ArgInfo.mode info)) (ψ : bProp (to-ctx Ξ'))
    → (to-ctx Ξ' ≡ ((to-ctx Ξ) ++tel (add-names (arg-tel info)) pfarg-names))
    → PCM (PCResult Ξ' ψ))
  → ProofCheckExt infos pfargs-names Ξ φ

record ProofExt : Set₁ where
  no-eta-equality
  field
    ProofExtCode : Mode → Set
    pf-code-tmarg-infos : (c : ProofExtCode m) → List (TmArgInfo m)
    pf-code-bparg-infos : (c : ProofExtCode m) → List (ArgInfo m)
    pf-code-pfarg-infos : (c : ProofExtCode m) → List (ArgInfo m)

    pf-code-check : (c : ProofExtCode m) (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ))
                    {tmarg-names : TmArgBoundNames (pf-code-tmarg-infos c)} (tmargs : ExtTmArgs (pf-code-tmarg-infos c) tmarg-names (to-ctx Ξ))
                    {bparg-names : ArgBoundNames (pf-code-bparg-infos c)} (bpargs : ExtBPArgs (pf-code-bparg-infos c) bparg-names (to-ctx Ξ))
                    (pfarg-names : ArgBoundNames (pf-code-pfarg-infos c)) →
                    ProofCheckExt (pf-code-pfarg-infos c) pfarg-names Ξ φ
