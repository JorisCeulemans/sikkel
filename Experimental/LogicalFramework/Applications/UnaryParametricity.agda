module Experimental.LogicalFramework.Applications.UnaryParametricity where

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


-- Final result: Using the fact that the term in the conclusion of
-- step 4 is β-equivalent to the term in the conclusion below.
final-prop : bProp {★} Γ
final-prop = ∀[ forget ∣ "a" ∈ EncBool ] ∀[ forget ∣ "b" ∈ EncBool ]
  Pred EncBool (mod⟨ forget ⟩ svar "a")
  ⊃ Pred EncBool (mod⟨ forget ⟩ svar "b")
  ⊃ Pred EncBool (∨'-forget ⊛ (mod⟨ forget ⟩ svar "a") ⊛ (mod⟨ forget ⟩ svar "b"))

final-proof : Proof {★} Γ
final-proof =
  ∀-intro[ forget ∣ "a" ∈ EncBool ] ∀-intro[ forget ∣ "b" ∈ EncBool ]
  ⊃-intro "preda" (⊃-intro "predb" (
  subst {x = "x"}
        (Pred EncBool (svar "x"))
        (let' mod⟨ forget ⟩ "f" ← lock𝟙-tm (f [ πʳ ]tmʳ) in' (mod⟨ forget ⟩ (svar "f" ∙ svar "b")))
        (∨'-forget ⊛ (mod⟨ forget ⟩ svar "a") ⊛ (mod⟨ forget ⟩ svar "b"))
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

final-test : IsOk (check-proof ◇ final-proof final-prop)
final-test = tt



{-
-- TODO: We could imagine wanting to prove the result below. In order
-- to do this, we need a better version of the proof rule
-- mod-induction (more similar to the MTT modal eliminator, where a
-- term of a boxed type gets substituted in the conclusion). This
-- could be implemented from the existing rule mod-induction, together
-- with a new principle allowing to substitute terms in proofs that
-- have a program variable in their context. The result below will
-- probably also allow for extraction by making ⟨ forget ∣ EncBool ⟩
-- extractable as ℕ.

∨'-nat : Tm {★} Γ (⟨ forget ∣ EncBool ⟩ ⇛ ⟨ forget ∣ EncBool ⟩ ⇛ ⟨ forget ∣ EncBool ⟩)
∨'-nat = mk-global-def "∨" (
  lam[ "a" ∈ ⟨ forget ∣ EncBool ⟩ ] lam[ "b" ∈ ⟨ forget ∣ EncBool ⟩ ] (∨'-forget ⊛ svar "a" ⊛ svar "b"))

some-other-prop : bProp {★} Γ
some-other-prop = ∀[ 𝟙 ∣ "a" ∈ ⟨ forget ∣ EncBool ⟩ ] ∀[ 𝟙 ∣ "b" ∈ ⟨ forget ∣ EncBool ⟩ ]
  Pred EncBool (svar "a")
  ⊃ Pred EncBool (svar "b")
  ⊃ Pred EncBool (∨'-nat ∙ svar "a" ∙ svar "b")

some-other-proof : Proof {★} Γ
some-other-proof =
  ∀-intro[ 𝟙 ∣ "a" ∈ ⟨ forget ∣ EncBool ⟩ ] ∀-intro[ 𝟙 ∣ "b" ∈ ⟨ forget ∣ EncBool ⟩ ]
  {!!}

some-other-test : IsOk (check-proof ◇ some-other-proof some-other-prop)
some-other-test = {!show-goals ◇ some-other-proof some-other-prop!}
-}
