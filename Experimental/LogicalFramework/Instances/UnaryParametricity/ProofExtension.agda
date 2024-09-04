module Experimental.LogicalFramework.Instances.UnaryParametricity.ProofExtension where

open import Data.List
open import Data.Product hiding (Σ)
open import Data.Unit
-- open import Relation.Binary.PropositionalEquality as Ag

open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Experimental.LogicalFramework.Instances.UnaryParametricity.MSTT
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.bPropExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.Soundness

open import Experimental.LogicalFramework.Proof.AlphaEquivalence unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Context unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
-- open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.ResultType unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
open import Experimental.LogicalFramework.bProp unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.Parameter.ArgInfo unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.Parameter.ProofExtension unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem

private variable
  m : Mode
  Γ : Ctx m
  T A B : Ty m


private
  bPred : (A : Ty ↑) → Tm Γ ⟨ forget ∣ A ⟩ → bProp Γ
  bPred A t = ext (bPred-code A) _ (t , _) tt tt

data ProofExtCode : Mode → Set where
  param-code : (A : Ty ↑) → ProofExtCode ★
  extent-from-code : (A B : Ty ↑) → ProofExtCode ★

pf-code-tmarg-infos : ProofExtCode m → List (TmArgInfo m)
pf-code-tmarg-infos (param-code A) = []
pf-code-tmarg-infos (extent-from-code A B) = tmarg-info ◇ ⟨ forget ∣ A ⇛ B ⟩ ∷ []

pf-code-bparg-infos : ProofExtCode m → List (ArgInfo m)
pf-code-bparg-infos (param-code A) = []
pf-code-bparg-infos (extent-from-code A B) = []

pf-code-pfarg-infos : ProofExtCode m → List (ArgInfo m)
pf-code-pfarg-infos (param-code A) = []
pf-code-pfarg-infos (extent-from-code A B) = arg-info ◇ ∷ []


pf-code-check : (c : ProofExtCode m) (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ))
                {tmarg-names : TmArgBoundNames (pf-code-tmarg-infos c)} (tmargs : ExtTmArgs (pf-code-tmarg-infos c) tmarg-names (to-ctx Ξ))
                {bparg-names : ArgBoundNames (pf-code-bparg-infos c)} (bpargs : ExtBPArgs (pf-code-bparg-infos c) bparg-names (to-ctx Ξ))
                (pfarg-names : ArgBoundNames (pf-code-pfarg-infos c)) →
                ProofCheckExt (pf-code-pfarg-infos c) pfarg-names Ξ φ
pf-code-check (param-code A) Ξ φ _ _ _ = do
  eφ ← φ ≟bprop (∀[ Σ ∣ "a" ∈ A ] bPred A (mod⟨ forget ⟩ var "a" π-cell))
  return ⟅ [] , _ ↦ param-sound Ξ A φ eφ ⟆
pf-code-check (extent-from-code A B) Ξ φ (f , tt) _ (tt , tt) check-subpf = do
  ⟅ goals , ⟦pf⟧ ⟆ ← check-subpf Ξ (bPred (A ⇛ B) f) refl
  eφ ← φ ≟bprop (∀[ forget ∣ "a" ∈ A ] bPred A (mod⟨ forget ⟩ svar "a")
                           ⊃ bPred B (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ in' mod⟨ forget ⟩ (svar "f" ∙ svar "a")))
  return ⟅ goals , sgls ↦ extent-from-sound Ξ A B φ f (⟦pf⟧ sgls) eφ ⟆


unary-param-pf-ext : ProofExt
ProofExt.ProofExtCode unary-param-pf-ext = ProofExtCode
ProofExt.pf-code-tmarg-infos unary-param-pf-ext = pf-code-tmarg-infos
ProofExt.pf-code-bparg-infos unary-param-pf-ext = pf-code-bparg-infos
ProofExt.pf-code-pfarg-infos unary-param-pf-ext = pf-code-pfarg-infos
ProofExt.pf-code-check unary-param-pf-ext = pf-code-check
