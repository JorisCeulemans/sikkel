--------------------------------------------------
-- Implementation of some proof helpers that semi-automate β-reduction
--------------------------------------------------

module Experimental.LogicalFramework.BetaReduction where

open import Data.Maybe
open import Data.Nat
open import Data.String

open import Experimental.LogicalFramework.STT
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Derivation

private variable
  Γ : CtxExpr
  T S : TyExpr
  x : String


--------------------------------------------------
-- Definition of a reduction function for STT (based on fuel)

data IsLam : TmExpr Γ T → Set where
  lam : (x : String) (b : TmExpr (Γ ,, x ∈ T) S) → IsLam (lam[ x ∈ T ] b)

is-lam : (t : TmExpr Γ T) → Maybe (IsLam t)
is-lam (lam[ x ∈ T ] b) = just (lam x b)
is-lam _ = nothing

data IsBoolVal : TmExpr Γ T → Set where
  true : ∀ {Γ} → IsBoolVal {Γ} true
  false : ∀ {Γ} → IsBoolVal {Γ} false

is-bool-val : (t : TmExpr Γ T) → Maybe (IsBoolVal t)
is-bool-val true = just true
is-bool-val false = just false
is-bool-val _ = nothing

data IsNatWHNF : TmExpr Γ T → Set where
  zero : ∀ {Γ} → IsNatWHNF {Γ} zero
  suc : (t : TmExpr Γ Nat') → IsNatWHNF (suc ∙ t)

is-nat-whnf : (t : TmExpr Γ T) → Maybe (IsNatWHNF t)
is-nat-whnf zero = just zero
is-nat-whnf (suc ∙ t) = just (suc t)
is-nat-whnf _ = nothing

data IsNatElim : TmExpr Γ T → Set where
  nat-elim : ∀ {A} (z : TmExpr Γ A) (s : TmExpr Γ (A ⇛ A)) → IsNatElim (nat-elim z s)

is-nat-elim : (t : TmExpr Γ T) → Maybe (IsNatElim t)
is-nat-elim (nat-elim z s) = just (nat-elim z s)
is-nat-elim _ = nothing

data IsPair : TmExpr Γ T → Set where
  pair : (t : TmExpr Γ T) (s : TmExpr Γ S) → IsPair (pair t s)

is-pair : (t : TmExpr Γ T) → Maybe (IsPair t)
is-pair (pair t s) = just (pair t s)
is-pair _ = nothing

-- The behaviour of step with term constructors like if or function
-- application, is to make a step in all subterms (given that no
-- special rules apply). We might make this customisable if that were
-- useful in some proofs.
step : TmExpr Γ T → TmExpr Γ T
step (var' x {v} {e}) = var' x {v} {e}
step (lam[ x ∈ T ] b) = lam[ x ∈ T ] b
step (f ∙ t) with is-lam f
step (.(lam[ x ∈ _ ] b) ∙ t)          | just (lam x b) = b [ t / x ]tm
step (f                 ∙ t         ) | nothing with is-nat-elim f | is-nat-whnf t
step (.(nat-elim z s)   ∙ .zero     ) | nothing | just (nat-elim z s) | just zero = z
step (.(nat-elim z s)   ∙ .(suc ∙ t)) | nothing | just (nat-elim z s) | just (suc t) = s ∙ (nat-elim z s ∙ t)
step (.(nat-elim z s)   ∙ t         ) | nothing | just (nat-elim z s) | nothing = (nat-elim z s) ∙ step t
step (f                 ∙ t         ) | nothing | nothing             | _ = step f ∙ step t
step zero = zero
step suc = suc
step (nat-elim z s) = nat-elim z s
step true = true
step false = false
step (if b t f) with is-bool-val b
step (if .true  t f) | just true = t
step (if .false t f) | just false = f
step (if b      t f) | nothing = if (step b) (step t) (step f)
step (pair t s) = pair (step t) (step s)
step (fst p) with is-pair p
step (fst .(pair t s)) | just (pair t s) = t
step (fst p          ) | nothing = fst (step p)
step (snd p) with is-pair p
step (snd .(pair t s)) | just (pair t s) = s
step (snd p          ) | nothing = snd (step p)

steps : ℕ → TmExpr Γ T → TmExpr Γ T
steps zero    t = t
steps (suc n) t = steps n (step t)


--------------------------------------------------
-- Proof that the step function is sound w.r.t. the proof system

step-sound : {Ξ : ProofCtx} (t : TmExpr (to-ctx Ξ) T) → Ξ ⊢ t ≡ᶠ step t
step-sound (var' x) = refl
step-sound (lam[ _ ∈ _ ] b) = refl
step-sound (f ∙ t) with is-lam f
step-sound (.(lam[ x ∈ _ ] b) ∙ t         ) | just (lam x b) = fun-β
step-sound (f                 ∙ t         ) | nothing with is-nat-elim f | is-nat-whnf t
step-sound (.(nat-elim z s)   ∙ .zero     ) | nothing | just (nat-elim z s) | just zero = nat-elim-β-zero
step-sound (.(nat-elim z s)   ∙ .(suc ∙ t)) | nothing | just (nat-elim z s) | just (suc t) = nat-elim-β-suc
step-sound (.(nat-elim z s)   ∙ t         ) | nothing | just (nat-elim z s) | nothing = cong _ (step-sound t)
step-sound (f                 ∙ t         ) | nothing | nothing             | _ = trans (cong f (step-sound t)) (fun-cong (step-sound f) _)
step-sound zero = refl
step-sound suc = refl
step-sound (nat-elim z s) = refl
step-sound true = refl
step-sound false = refl
step-sound (if b t f) with is-bool-val b
step-sound (if .true  t f) | just true = if-β-true
step-sound (if .false t f) | just false = if-β-false
step-sound (if b      t f) | nothing = if-cong (step-sound b) (step-sound t) (step-sound f)
step-sound (pair t s) = pair-cong (step-sound t) (step-sound s)
step-sound (fst p) with is-pair p
step-sound (fst .(pair t s)) | just (pair t s) = pair-β-fst
step-sound (fst p          ) | nothing = fst-cong (step-sound p)
step-sound (snd p) with is-pair p
step-sound (snd .(pair t s)) | just (pair t s) = pair-β-snd
step-sound (snd p          ) | nothing = snd-cong (step-sound p)

steps-sound : (n : ℕ) {Ξ : ProofCtx} (t : TmExpr (to-ctx Ξ) T) → Ξ ⊢ t ≡ᶠ steps n t
steps-sound zero    t = refl
steps-sound (suc n) t = trans (step-sound t) (steps-sound n _)


--------------------------------------------------
-- Some proof schemes based on reduction
--   Note that for termination reasons, you must provide the maximal
--   number of reduction steps.

reduce : (n : ℕ) {Ξ : ProofCtx} {t : TmExpr (to-ctx Ξ) T} → Ξ ⊢ t ≡ᶠ steps n t
reduce n = steps-sound n _

with-reduce-left : (n : ℕ) {Ξ : ProofCtx} {t s : TmExpr (to-ctx Ξ) T} → Ξ ⊢ steps n t ≡ᶠ s → Ξ ⊢ t ≡ᶠ s
with-reduce-left n d = trans (steps-sound n _) d

with-reduce-right : (n : ℕ) {Ξ : ProofCtx} {t s : TmExpr (to-ctx Ξ) T} → Ξ ⊢ t ≡ᶠ steps n s → Ξ ⊢ t ≡ᶠ s
with-reduce-right n d = trans d (sym (steps-sound n _))

with-reduce : (n : ℕ) {Ξ : ProofCtx} {t s : TmExpr (to-ctx Ξ) T} → Ξ ⊢ steps n t ≡ᶠ steps n s → Ξ ⊢ t ≡ᶠ s
with-reduce n d = with-reduce-left n (with-reduce-right n d)
