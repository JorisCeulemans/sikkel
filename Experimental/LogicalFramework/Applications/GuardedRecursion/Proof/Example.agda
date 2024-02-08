module Experimental.LogicalFramework.Applications.GuardedRecursion.Proof.Example where

open import Experimental.LogicalFramework.Instances.GuardedRecursion
open import Experimental.LogicalFramework.Applications.GuardedRecursion.Examples


private variable
  m n : Mode
  Γ Δ : Ctx m
  A B T S : Ty m


g-cons-cong : (h1 h2 : Tm (Γ ,lock⟨ constantly ⟩) A) (t1 t2 : Tm (Γ ,lock⟨ later ⟩) (GStream A)) →
              Proof (Γ ,lock⟨ constantly ⟩) → Proof (Γ ,lock⟨ later ⟩) → Proof Γ
g-cons-cong h1 h2 t1 t2 ph pt =
  trans (g-cons h2 t1)
    (subst {x = "dummy"} (g-cons (h1 [ π ,slock⟨ constantly ⟩ ]tm) (t1 [ π ,slock⟨ later ⟩ ]tm) ≡ᵇ g-cons v0 (t1 [ π ,slock⟨ later ⟩ ]tm)) h1 h2 ph refl)
    (subst {x = "dummy"} (g-cons (h2 [ π ,slock⟨ constantly ⟩ ]tm) (t1 [ π ,slock⟨ later ⟩ ]tm) ≡ᵇ g-cons (h2 [ π ,slock⟨ constantly ⟩ ]tm) v0) t1 t2 pt refl)

test : Proof ◇
test = g-cons-cong zero zero g-zeros g-zeros refl refl

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality as Ag

check-proof-nosem : (Ξ : ProofCtx m) → Proof (to-ctx Ξ) → bProp (to-ctx Ξ) → PCM (List Goal)
check-proof-nosem Ξ p φ = PCResult.goals <$> check-proof Ξ p φ

_ : check-proof-nosem ◇ test (g-cons zero g-zeros ≡ᵇ g-cons zero g-zeros) ≡ PCM.ok []
_ = Ag.refl

_ : check-proof-nosem ◇ gstream-β-tail (g-tail (g-cons zero g-zeros) ≡ᵇ mod⟨ later ⟩ g-zeros) ≡ PCM.ok []
_ = Ag.refl
