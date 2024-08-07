module Experimental.LogicalFramework.Applications.GuardedRecursion.Examples where

open import Data.Nat
open import Data.Vec using ([]; _∷_)
open import Function
open import Relation.Binary.PropositionalEquality as Ag

open import Preliminaries
open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT

private variable
  m n : Mode
  Γ Δ : Ctx m
  A B : Ty m


g-map : Tm Γ (⟨ constantly ∣ A ⇛ B ⟩⇛ GStream A ⇛ GStream B)
g-map {A = A} {B} =
  lam[ constantly ∣ "f" ∈ A ⇛ B ]
    löb[later∣ "m" ∈ GStream A ⇛ GStream B ]
      lam[ "s" ∈ GStream A ]
        let' mod⟨ constantly ⟩ "head-s" ← g-head (svar "s") in'
        let' mod⟨ later ⟩ "tail-s" ← g-tail (svar "s") in' (
        g-cons (svar "f" ∙ svar "head-s")
               (svar "m" ∙ svar "tail-s"))

g-iterate : Tm Γ (⟨ later ⓜ constantly ∣ A ⇛ A ⟩⇛ ⟨ constantly ∣ A ⟩⇛ GStream A)
g-iterate {A = A} = lam[ later ⓜ constantly ∣ "f" ∈ A ⇛ A ]
  lam[ constantly ∣ "a" ∈ A ] löb[later∣ "s" ∈ GStream A ]
  g-cons (svar "a")
         (g-map ∙ svar "f" ∙ svar "s")

g-iterate' : Tm Γ (⟨ later ⓜ constantly ∣ A ⇛ A ⟩⇛ ⟨ constantly ∣ A ⟩⇛ GStream A)
g-iterate' {A = A} = lam[ later ⓜ constantly ∣ "f" ∈ A ⇛ A ]
  löb[later∣ "it" ∈ ⟨ constantly ∣ A ⟩⇛ GStream A ]
  lam[ constantly ∣ "a" ∈ A ]
    g-cons (svar "a")
           (svar "it" ∙ (svar "f" ∙ var "a" (𝟙≤ltr ⓣ-hor id-cell {μ = constantly})))


g-zeros : Tm Γ (GStream Nat')
g-zeros = löb[later∣ "zeros" ∈ GStream Nat' ] g-cons zero (svar "zeros")

Stream' : Ty ★ → Ty ★
Stream' A = ⟨ forever ∣ GStream A ⟩

zeros : Tm Γ (Stream' Nat')
zeros = mk-global-def "zeros" $
  mod⟨ forever ⟩ g-zeros

zeros-extract : Stream ℕ
zeros-extract = extract-tm-◇ zeros

test-zeros-extract :
  take 10 zeros-extract ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
test-zeros-extract = Ag.refl

nats : Tm Γ (Stream' Nat')
nats = mk-global-def "nat" $
  mod⟨ forever ⟩ (g-iterate ∙ (lam[ "n" ∈ Nat' ] suc (svar "n")) ∙ zero)

nats-extract : Stream ℕ
nats-extract = extract-tm-◇ nats

nats-extract-test :
  take 10 nats-extract ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
nats-extract-test = Ag.refl


head' : Tm Γ (Stream' A ⇛ A)
head' {A = A} =
  lam[ "s" ∈ Stream' A ]
    let' mod⟨ forever ⟩ "g-s" ← svar "s" in'
    triv⁻¹ (comp (mod⟨ forever ⟩
    let' mod⟨ constantly ⟩ "head-s" ← g-head (svar "g-s") in' (mod⟨ constantly ⟩ svar "head-s")))

iterate : Tm Γ ((A ⇛ A) ⇛ A ⇛ Stream' A)
iterate {A = A} = mk-global-def "iterate" (
  lam[ "f" ∈ A ⇛ A ] (lam[ "a" ∈ A ] (mod⟨ forever ⟩ (g-iterate ∙ svar "f" ∙ svar "a"))))

iterate' : Tm Γ ((A ⇛ A) ⇛ A ⇛ Stream' A)
iterate' {A = A} = mk-global-def "iterate'" (
  lam[ "f" ∈ A ⇛ A ] (lam[ "a" ∈ A ] (mod⟨ forever ⟩ (g-iterate' ∙ svar "f" ∙ svar "a"))))

iterateℕ iterate'ℕ : (ℕ → ℕ) → ℕ → Stream ℕ
iterateℕ = extract-tm-◇ (iterate {A = Nat'})
iterate'ℕ = extract-tm-◇ (iterate' {A = Nat'})

iterate'ℕ-test :
  take 10 (iterate'ℕ (2 *_) 1) ≡ 1 ∷ 2 ∷ 4 ∷ 8 ∷ 16 ∷ 32 ∷ 64 ∷ 128 ∷ 256 ∷ 512 ∷ []
iterate'ℕ-test = Ag.refl
