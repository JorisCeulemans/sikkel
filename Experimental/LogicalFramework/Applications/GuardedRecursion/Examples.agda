module Experimental.LogicalFramework.Applications.GuardedRecursion.Examples where

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
           (svar "it" ∙ (svar "f" ∙ var "a" (𝟙≤ltr ⓣ-hor id-cell)))


g-zeros : Tm Γ (GStream Nat')
g-zeros = löb[later∣ "zeros" ∈ GStream Nat' ] g-cons zero (svar "zeros")

Stream' : Ty ★ → Ty ★
Stream' A = ⟨ forever ∣ GStream A ⟩

zeros : Tm Γ (Stream' Nat')
zeros = mod⟨ forever ⟩ g-zeros


head' : Tm Γ (Stream' A ⇛ A)
head' {A = A} =
  lam[ "s" ∈ Stream' A ]
    let' mod⟨ forever ⟩ "g-s" ← svar "s" in'
    triv⁻¹ (comp (mod⟨ forever ⟩
    let' mod⟨ constantly ⟩ "head-s" ← g-head (svar "g-s") in' (mod⟨ constantly ⟩ svar "head-s")))
