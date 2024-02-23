module Experimental.LogicalFramework.Instances.GuardedRecursion.ProofExtension where

open import Data.List
open import Data.Product
open import Data.String as Str using (String)
open import Relation.Binary.PropositionalEquality as Ag

open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.bPropExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.Soundness

open import Experimental.LogicalFramework.Proof.Equality guarded-mstt guarded-bp-ext
open import Experimental.LogicalFramework.Proof.Context guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.ResultType guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.bProp guarded-mstt guarded-bp-ext guarded-bp-ext-sem

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension guarded-mt guarded-ty-ext String
open import Experimental.LogicalFramework.Parameter.ArgInfo guarded-mt guarded-ty-ext String
open import Experimental.LogicalFramework.Parameter.ProofExtension guarded-mstt guarded-bp-ext guarded-bp-ext-sem

private variable
  m : Mode
  Γ : Ctx m
  T A B : Ty m


data ProofExtCode : Mode → Set where
  gstream-β-head-code gstream-β-tail-code : ProofExtCode ω
  tmlöb-β-code : ProofExtCode ω
  pflöb-code : (x : String) → ProofExtCode ω

pf-code-tmarg-infos : ProofExtCode m → List (TmArgInfo m)
pf-code-tmarg-infos gstream-β-head-code = []
pf-code-tmarg-infos gstream-β-tail-code = []
pf-code-tmarg-infos tmlöb-β-code = []
pf-code-tmarg-infos (pflöb-code x) = []

pf-code-bparg-infos : ProofExtCode m → List (ArgInfo m)
pf-code-bparg-infos gstream-β-head-code = []
pf-code-bparg-infos gstream-β-tail-code = []
pf-code-bparg-infos tmlöb-β-code = []
pf-code-bparg-infos (pflöb-code x) = []

pf-code-pfarg-infos : ProofExtCode m → List (ArgInfo m)
pf-code-pfarg-infos gstream-β-head-code = []
pf-code-pfarg-infos gstream-β-tail-code = []
pf-code-pfarg-infos tmlöb-β-code = []
pf-code-pfarg-infos (pflöb-code x) =
  arg-info ◇ ∷
  []


data IsGHead : Tm Γ T → Set where
  is-g-head : ∀ {A} (s : Tm Γ (GStream A)) → IsGHead (g-head s)

is-g-head? : (t : Tm Γ T) → PCM (IsGHead t)
is-g-head? (g-head s) = return (is-g-head s)
is-g-head? _ = throw-error "head of guarded stream expected"

data IsGTail : Tm Γ T → Set where
  is-g-tail : ∀ {A} (s : Tm Γ (GStream A)) → IsGTail (g-tail s)

is-g-tail? : (t : Tm Γ T) → PCM (IsGTail t)
is-g-tail? (g-tail s) = return (is-g-tail s)
is-g-tail? _ = throw-error "tail of guarded stream expected"

data IsGCons : Tm Γ T → Set where
  is-g-cons : ∀ {A} (a : Tm (Γ ,lock⟨ constantly ⟩) A) (s : Tm (Γ ,lock⟨ later ⟩) (GStream A)) → IsGCons (g-cons a s)

is-g-cons? : (t : Tm Γ T) → PCM (IsGCons t)
is-g-cons? (g-cons a s) = return (is-g-cons a s)
is-g-cons? _ = throw-error "cons of guarded stream expected"

data IsLob : Tm Γ T → Set where
  is-lob : (x : String) (T : Ty ω) (t : Tm (Γ ,, later ∣ x ∈ T) T) → IsLob (löb[later∣ x ∈ T ] t)

is-lob? : (t : Tm Γ T) → PCM (IsLob t)
is-lob? (löb[later∣ x ∈ T ] t) = return (is-lob x T t)
is-lob? _ = throw-error "löb induction expected"


pf-code-check : (c : ProofExtCode m) (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) →
                ExtTmArgs (pf-code-tmarg-infos c) (to-ctx Ξ) →
                ExtBPArgs (pf-code-bparg-infos c) (to-ctx Ξ) →
                ProofCheckExt (pf-code-pfarg-infos c) Ξ φ
pf-code-check gstream-β-head-code Ξ φ _ _ = do
  is-eq lhs rhs ← is-eq? φ
  is-g-head s ← is-g-head? lhs
  is-g-cons h t ← is-g-cons? s
  refl ← rhs ≟tm (mod⟨ constantly ⟩ h)
  return ⟅ [] , _ ↦ gstream-β-head-sound Ξ h t ⟆
pf-code-check gstream-β-tail-code Ξ φ _ _ = do
  is-eq lhs rhs ← is-eq? φ
  is-g-tail tail-arg ← is-g-tail? lhs
  is-g-cons h t ← is-g-cons? tail-arg
  refl ← rhs ≟tm (mod⟨ later ⟩ t)
  return ⟅ [] , _ ↦ gstream-β-tail-sound Ξ h t ⟆
pf-code-check tmlöb-β-code Ξ φ _ _ = do
  is-eq lhs rhs ← is-eq? φ
  is-lob x T t ← is-lob? lhs
  refl ← rhs ≟tm (t [ rename-tm ((löb[later∣ x ∈ T ] t)) (key-ren (◇ ,lock⟨ later ⟩) ◇ 𝟙≤ltr) / x ]tm)
  return ⟅ [] , _ ↦ tmlöb-β-sound Ξ x t ⟆
pf-code-check (pflöb-code x) Ξ φ _ _ = λ check-subpf → do
  ⟅ goals , ⟦p⟧ ⟆ ← check-subpf (Ξ ,,ᵇ later ∣ x ∈ rename-bprop φ (key-ren (◇ ,lock⟨ later ⟩) ◇ 𝟙≤ltr)) φ Ag.refl
  return ⟅ goals , sgoals ↦ pf-löb-sound Ξ φ x (⟦p⟧ sgoals) ⟆

guarded-pf-ext : ProofExt
ProofExt.ProofExtCode guarded-pf-ext = ProofExtCode
ProofExt.pf-code-tmarg-infos guarded-pf-ext = pf-code-tmarg-infos
ProofExt.pf-code-bparg-infos guarded-pf-ext = pf-code-bparg-infos
ProofExt.pf-code-pfarg-infos guarded-pf-ext = pf-code-pfarg-infos
ProofExt.pf-code-check guarded-pf-ext = pf-code-check
