module Experimental.LogicalFramework.Applications.UnaryParametricity where

open import Data.Nat
open import Data.Unit

open import Experimental.LogicalFramework.Instances.UnaryParametricity

private variable
  m n : Mode
  Γ : Ctx m


-- We can implement disjunction for our encoding of booleans out of
-- the primitive negation and conjunction.
-- We will then prove further on that disjunction preserves
-- booleanness (i.e. the parametricity predicate associated to
-- EncBool). Note that this proof could be made shorter, but we
-- construct it in several steps for clarity.
∨' : Tm {↑} Γ (EncBool ⇛ EncBool ⇛ EncBool)
∨' = lam[ "x" ∈ EncBool ] (lam[ "y" ∈ EncBool ] (¬' ∙ (∧' ∙ (¬' ∙ svar "x") ∙ (¬' ∙ svar "y"))))


∨'-forget : Tm {★} Γ ⟨ forget ∣ EncBool ⇛ EncBool ⇛ EncBool ⟩
∨'-forget = mod⟨ forget ⟩ ∨'

∨'-★ : Tm {★} Γ (⟨ forget ∣ EncBool ⟩ ⇛ ⟨ forget ∣ EncBool ⟩ ⇛ ⟨ forget ∣ EncBool ⟩)
∨'-★ = mk-global-def "∨" (
  lam[ "a" ∈ ⟨ forget ∣ EncBool ⟩ ] lam[ "b" ∈ ⟨ forget ∣ EncBool ⟩ ] (∨'-forget ⊛ svar "a" ⊛ svar "b"))

∨'-agda : ℕ → ℕ → ℕ
∨'-agda = extract-tm-◇ ∨'-★


-- Step 1: Applying the parametricity principle to ∨'-forget
step1-prop : bProp {★} Γ
step1-prop = Pred (EncBool ⇛ EncBool ⇛ EncBool) ∨'-forget

step1-proof : Proof {★} Γ
step1-proof = ∀-elim Σ
  (∀[ Σ ∣ "f" ∈ EncBool ⇛ EncBool ⇛ EncBool ] Pred (EncBool ⇛ EncBool ⇛ EncBool) (mod⟨ forget ⟩ var "f" π-cell))
  (param (EncBool ⇛ EncBool ⇛ EncBool))
  ∨'

step1-test : IsOk (check-proof ◇ step1-proof step1-prop)
step1-test = tt


-- Step 2: Using extent-from once for the parametricity predicate for
-- the type EncBool ⇛ (EncBool ⇛ EncBool)
f : Tm (Γ ,, forget ∣ "a" ∈ EncBool) ⟨ forget ∣ EncBool ⇛ EncBool ⟩
f = let' mod⟨ forget ⟩ "f" ← ∨'-forget [ πʳ ]tmʳ in' (mod⟨ forget ⟩ (svar "f" ∙ svar "a"))

step2-prop : bProp {★} Γ
step2-prop = ∀[ forget ∣ "a" ∈ EncBool ] Pred EncBool (mod⟨ forget ⟩ svar "a") ⊃ Pred (EncBool ⇛ EncBool) f

step2-proof : Proof {★} Γ
step2-proof = extent-from EncBool (EncBool ⇛ EncBool) ∨'-forget step1-proof

step2-test : IsOk (check-proof ◇ step2-proof step2-prop)
step2-test = tt


-- Step 3: Again using extent-from, now for the parametricity
-- predicate for the type EncBool ⇛ EncBool
step3-prop : bProp {★} Γ
step3-prop = ∀[ forget ∣ "a" ∈ EncBool ]
  Pred EncBool (mod⟨ forget ⟩ svar "a")
  ⊃ (∀[ forget ∣ "b" ∈ EncBool ]
        Pred EncBool (mod⟨ forget ⟩ svar "b") ⊃ Pred EncBool (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ in' (mod⟨ forget ⟩ (svar "f" ∙ svar "b"))))

step3-proof : Proof {★} Γ
step3-proof = ∀-intro[ forget ∣ "a" ∈ EncBool ] ⊃-intro "preda" (
  extent-from EncBool EncBool f (
    ⊃-elim 𝟙 (Pred EncBool (mod⟨ forget ⟩ svar "a")) (∀-elim forget step2-prop step2-proof (svar "a")) (assumption' "preda" {μ = 𝟙} id-cell)))

step3-test : IsOk (check-proof ◇ step3-proof step3-prop)
step3-test = tt


-- Step 4: Rearranging the universal quantifiers and the assumptions
-- about "a" and "b".
step4-prop : bProp {★} Γ
step4-prop = ∀[ forget ∣ "a" ∈ EncBool ] ∀[ forget ∣ "b" ∈ EncBool ]
  Pred EncBool (mod⟨ forget ⟩ svar "a")
  ⊃ Pred EncBool (mod⟨ forget ⟩ svar "b")
  ⊃ Pred EncBool (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ in' (mod⟨ forget ⟩ (svar "f" ∙ svar "b")))

step4-proof : Proof {★} Γ
step4-proof =
  ∀-intro[ forget ∣ "a" ∈ EncBool ] ∀-intro[ forget ∣ "b" ∈ EncBool ]
  ⊃-intro "preda" (
  ∀-elim
    forget
    (∀[ forget ∣ "b" ∈ EncBool ] Pred EncBool (mod⟨ forget ⟩ svar "b")
               ⊃ Pred EncBool (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ [ πʳ ]tmʳ in' (mod⟨ forget ⟩ (svar "f" ∙ svar "b"))))
    (⊃-elim 𝟙 (Pred EncBool (mod⟨ forget ⟩ svar "a")) (∀-elim forget step3-prop step3-proof (svar "a")) (assumption' "preda" {μ = 𝟙} id-cell))
    (svar "b"))

step4-test : IsOk (check-proof ◇ step4-proof step4-prop)
step4-test = tt


-- Step 5: Using the fact that the term in the conclusion of
-- step 4 is β-equivalent to the term in the conclusion below.
step5-prop : bProp {★} Γ
step5-prop = ∀[ forget ∣ "a" ∈ EncBool ] ∀[ forget ∣ "b" ∈ EncBool ]
  Pred EncBool (mod⟨ forget ⟩ svar "a")
  ⊃ Pred EncBool (mod⟨ forget ⟩ svar "b")
  ⊃ Pred EncBool (∨'-★ ∙ (mod⟨ forget ⟩ svar "a") ∙ (mod⟨ forget ⟩ svar "b"))

step5-proof : Proof {★} Γ
step5-proof =
  ∀-intro[ forget ∣ "a" ∈ EncBool ] ∀-intro[ forget ∣ "b" ∈ EncBool ]
  ⊃-intro "preda" (⊃-intro "predb" (
  subst {x = "x"}
        (Pred EncBool (svar "x"))
        (let' mod⟨ forget ⟩ "f" ← lock𝟙-tm (f [ πʳ ]tmʳ) in' (mod⟨ forget ⟩ (svar "f" ∙ svar "b")))
        (∨'-★ ∙ (mod⟨ forget ⟩ svar "a") ∙ (mod⟨ forget ⟩ svar "b"))
        by-normalization
        (⊃-elim 𝟙 (Pred EncBool (mod⟨ forget ⟩ svar "b")) (⊃-elim 𝟙 (Pred EncBool (mod⟨ forget ⟩ svar "a")) (
          ∀-elim forget
                 (∀[ forget ∣ "b" ∈ EncBool ] Pred EncBool (mod⟨ forget ⟩ svar "a")
                      ⊃ Pred EncBool (mod⟨ forget ⟩ svar "b")
                      ⊃ Pred EncBool (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ [ πʳ ]tmʳ in' (mod⟨ forget ⟩ (svar "f" ∙ svar "b"))))
                 (∀-elim forget step4-prop step4-proof (svar "a"))
                 (svar "b"))
          (assumption' "preda" {μ = 𝟙} id-cell))
          (assumption' "predb" {μ = 𝟙} id-cell))))

step5-test : IsOk (check-proof ◇ step5-proof step5-prop)
step5-test = tt


-- Final step: Using modal induction to show a variant of step5-prop
-- for ∨'-★.
final-prop : bProp {★} Γ
final-prop = ∀[ 𝟙 ∣ "a" ∈ ⟨ forget ∣ EncBool ⟩ ] ∀[ 𝟙 ∣ "b" ∈ ⟨ forget ∣ EncBool ⟩ ]
  Pred EncBool (svar "a")
  ⊃ Pred EncBool (svar "b")
  ⊃ Pred EncBool (∨'-★ ∙ svar "a" ∙ svar "b")

final-proof : Proof {★} Γ
final-proof =
  ∀-intro[ 𝟙 ∣ "a" ∈ ⟨ forget ∣ EncBool ⟩ ] ∀-intro[ 𝟙 ∣ "b" ∈ ⟨ forget ∣ EncBool ⟩ ]
  mod-induction forget 𝟙 "y" (
  ∀-elim 𝟙 (∀[ 𝟙 ∣ "â" ∈ ⟨ forget ∣ EncBool ⟩ ]
               Pred EncBool (svar "â") ⊃ Pred EncBool (mod⟨ forget ⟩ svar "y") ⊃ Pred EncBool (∨'-★ ∙ svar "â" ∙ (mod⟨ forget ⟩ svar "y")))
         (∀-intro[ 𝟙 ∣ "â" ∈ ⟨ forget ∣ EncBool ⟩ ]
           mod-induction forget 𝟙 "x"
           (∀-elim forget (∀[ forget ∣ "b" ∈ EncBool ]
                              Pred EncBool (mod⟨ forget ⟩ svar "x")
                              ⊃ Pred EncBool (mod⟨ forget ⟩ svar "b")
                              ⊃ Pred EncBool (∨'-★ ∙ (mod⟨ forget ⟩ svar "x") ∙ (mod⟨ forget ⟩ svar "b")))
             (∀-elim forget step5-prop step5-proof (svar "x"))
             (svar "y")))
         (svar "a"))

final-test : IsOk (check-proof ◇ final-proof final-prop)
final-test = tt

open import Applications.UnaryParametricity.Model
open import Relation.Binary.PropositionalEquality as Ag

final-test-extract : _
final-test-extract = extract-proof-◇ final-proof final-prop {tt} {tt}

extract-correct-type : extract-bprop {◇} final-prop tt ≡ ((m n : ℕ) → IsBit m → IsBit n → IsBit (∨'-agda m n))
extract-correct-type = Ag.refl

{-



-}
