open import Data.String
open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.Parameter.ProofExtension
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 String 𝓉)
  -- (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 _ _)
  where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 String
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 String

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.Proof.CheckingMonad

private variable
  m : Mode



record ProofExt : Set₁ where
  field
    ProofExtCode : Mode → Set
    _≟pf-code_ : (c1 c2 : ProofExtCode m) → PCM (c1 ≡ c2)
    pf-code-tmarg-infos : (c : ProofExtCode m) → List (TmArgInfo m)
    pf-code-bparg-infos : (c : ProofExtCode m) → List (ArgInfo m)
    pf-code-pfarg-infos : (c : ProofExtCode m) → List (ArgInfo m)
