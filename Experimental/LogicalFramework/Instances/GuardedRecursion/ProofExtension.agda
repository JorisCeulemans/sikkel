module Experimental.LogicalFramework.Instances.GuardedRecursion.ProofExtension where

open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality as Ag

open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.bPropExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.Soundness

open import Experimental.LogicalFramework.Proof.AlphaEquivalence guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Context guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.ResultType guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.bProp guarded-mstt guarded-bp-ext guarded-bp-ext-sem

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.Parameter.ArgInfo guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.Parameter.ProofExtension guarded-mstt guarded-bp-ext guarded-bp-ext-sem

private variable
  m : Mode
  Γ : Ctx m
  T A B : Ty m


data ProofExtCode : Mode → Set where
  tmlöb-β-code : ProofExtCode ω
  pflöb-code : (x : Name) → ProofExtCode ω

pf-code-tmarg-infos : ProofExtCode m → List (TmArgInfo m)
pf-code-tmarg-infos tmlöb-β-code = []
pf-code-tmarg-infos (pflöb-code x) = []

pf-code-bparg-infos : ProofExtCode m → List (ArgInfo m)
pf-code-bparg-infos tmlöb-β-code = []
pf-code-bparg-infos (pflöb-code x) = []

pf-code-pfarg-infos : ProofExtCode m → List (ArgInfo m)
pf-code-pfarg-infos tmlöb-β-code = []
pf-code-pfarg-infos (pflöb-code x) =
  arg-info ◇ ∷
  []


data IsLob : Tm Γ T → Set where
  is-lob : (x : Name) (T : Ty ω) (t : Tm (Γ ,, later ∣ x ∈ T) T) → IsLob (löb[later∣ x ∈ T ] t)

is-lob? : (t : Tm Γ T) → PCM (IsLob t)
is-lob? (löb[later∣ x ∈ T ] t) = return (is-lob x T t)
is-lob? _ = throw-error "löb induction expected"


pf-code-check : (c : ProofExtCode m) (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ))
                {tmarg-names : TmArgBoundNames (pf-code-tmarg-infos c)} (tmargs : ExtTmArgs (pf-code-tmarg-infos c) tmarg-names (to-ctx Ξ))
                {bparg-names : ArgBoundNames (pf-code-bparg-infos c)} (bpargs : ExtBPArgs (pf-code-bparg-infos c) bparg-names (to-ctx Ξ))
                (pfarg-names : ArgBoundNames (pf-code-pfarg-infos c)) →
                ProofCheckExt (pf-code-pfarg-infos c) pfarg-names Ξ φ
pf-code-check tmlöb-β-code Ξ φ _ _ _ = do
  is-eq lhs rhs ← is-eq? φ
  is-lob x T t ← is-lob? lhs
  e-rhs ← rhs ≟tm (t [ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ]tmˢ)
  return ⟅ [] , _ ↦ tmlöb-β-sound Ξ x t rhs e-rhs ⟆
pf-code-check (pflöb-code x) Ξ φ _ _ (_ , _) = λ check-subpf → do
  ⟅ goals , ⟦p⟧ ⟆ ← check-subpf (Ξ ,,ᵇ later ∣ x ∈ φ [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]bpropʳ) φ Ag.refl
  return ⟅ goals , sgoals ↦ pf-löb-sound Ξ φ x (⟦p⟧ sgoals) ⟆

guarded-pf-ext : ProofExt
ProofExt.ProofExtCode guarded-pf-ext = ProofExtCode
ProofExt.pf-code-tmarg-infos guarded-pf-ext = pf-code-tmarg-infos
ProofExt.pf-code-bparg-infos guarded-pf-ext = pf-code-bparg-infos
ProofExt.pf-code-pfarg-infos guarded-pf-ext = pf-code-pfarg-infos
ProofExt.pf-code-check guarded-pf-ext = pf-code-check
