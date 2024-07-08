module Experimental.LogicalFramework.Applications.GuardedRecursion.Proof.Example where

open import Data.Unit

open import Experimental.LogicalFramework.Instances.GuardedRecursion
open import Experimental.LogicalFramework.Applications.GuardedRecursion.Examples


private variable
  m n : Mode
  Γ Δ : Ctx m
  A B T S : Ty m


-- Ξ ,lock⟨ constantly ⟩ ⊢ h1 ≡ᵇ h2
-- Ξ ,lock⟨ later ⟩ ⊢ t1 ≡ᵇ t2
-- --------------------------------
-- Ξ ⊢ g-cons h1 t1 ≡ᵇ g-cons h2 t2
g-cons-cong : (h1 h2 : Tm (Γ ,lock⟨ constantly ⟩) A) (t1 t2 : Tm (Γ ,lock⟨ later ⟩) (GStream A)) →
              Proof (Γ ,lock⟨ constantly ⟩) → Proof (Γ ,lock⟨ later ⟩) → Proof Γ
g-cons-cong h1 h2 t1 t2 ph pt =
  trans (g-cons h2 t1)
    (subst {x = "dummy"} (g-cons (h1 [ πʳ ,lockʳ⟨ constantly ⟩ ]tmʳ) (t1 [ πʳ ,lockʳ⟨ later ⟩ ]tmʳ) ≡ᵇ g-cons v0 (t1 [ πʳ ,lockʳ⟨ later ⟩ ]tmʳ)) h1 h2 ph refl)
    (subst {x = "dummy"} (g-cons (h2 [ πʳ ,lockʳ⟨ constantly ⟩ ]tmʳ) (t1 [ πʳ ,lockʳ⟨ later ⟩ ]tmʳ) ≡ᵇ g-cons (h2 [ πʳ ,lockʳ⟨ constantly ⟩ ]tmʳ) v0) t1 t2 pt refl)

-- Some 2-cell abbreviations
γ : TwoCell constantly (later ⓜ constantly)
γ = 𝟙≤ltr ⓣ-hor id-cell {μ = constantly}

δ : TwoCell constantly (later ⓜ (later ⓜ constantly))
δ = 𝟙≤ltr {0} ⓣ-hor γ


g-map-cons : bProp (Γ ,, constantly ∣ "f" ∈ (A ⇛ A) ,, constantly ∣ "h" ∈ A ,, later ∣ "s" ∈ (GStream A))
g-map-cons = g-map ∙ svar "f" ∙ g-cons (svar "h") (svar "s")
               ≡ᵇ
             g-cons (svar "f" ∙ svar "h") (g-map ∙ var "f" γ ∙ svar "s")

g-map-cons-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-map-cons-proof A =
  ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ]
  ∀-intro[ constantly ∣ "h" ∈ A ]
  ∀-intro[ later ∣ "s" ∈ GStream A ]
  equality-chain
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-map ∙ svar "f" ∙ g-cons (svar "h") (svar "s")
      ≡ᵇ⟨ fun-cong {μ = 𝟙} (with-normalization tmlöb-β) (g-cons (svar "h") (svar "s")) ⟩
        (lam[ "as" ∈ GStream A ]
          let' mod⟨ constantly ⟩ "head-as" ← g-head (svar "as") in'
          let' mod⟨ later ⟩ "tail-as" ← g-tail (svar "as") in' (
          g-cons (svar "f" ∙ svar "head-as")
                 (g-map ∙ var "f" γ ∙ svar "tail-as")))
        ∙ g-cons (svar "h") (svar "s")
      ≡ᵇ⟨ by-normalization ⟩
        g-cons (svar "f" ∙ svar "h") (g-map ∙ var "f" γ ∙ svar "s") ∎

test-g-map-cons : IsOk (check-proof ◇ (g-map-cons-proof Nat') (∀[ constantly ∣ "f" ∈ Nat' ⇛ Nat' ] ∀[ constantly ∣ "h" ∈ Nat' ] ∀[ later ∣ "s" ∈ GStream Nat' ] g-map-cons))
test-g-map-cons = tt


g-iterate'-cons : bProp (Γ ,, constantly ∣ "f" ∈ (A ⇛ A) ,, constantly ∣ "a" ∈ A)
g-iterate'-cons = g-iterate' ∙ var "f" γ ∙ svar "a"
                    ≡ᵇ
                  g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))

g-iterate'-cons-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-iterate'-cons-proof A = ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ] ∀-intro[ constantly ∣ "a" ∈ A ] equality-chain
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-iterate' ∙ var "f" γ ∙ svar "a"
      ≡ᵇ⟨ fun-cong (with-normalization tmlöb-β) (svar "a") ⟩
        (lam[ constantly ∣ "a" ∈ A ] g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
        ∙ svar "a"
      ≡ᵇ⟨ by-normalization ⟩
        g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)) ∎

test-g-iterate'-cons : IsOk (check-proof ◇ (g-iterate'-cons-proof Nat') (∀[ constantly ∣ "f" ∈ Nat' ⇛ Nat' ] ∀[ constantly ∣ "a" ∈ Nat' ] g-iterate'-cons))
test-g-iterate'-cons = tt


g-map-iterate : bProp (Γ ,, constantly ∣ "f" ∈ (A ⇛ A) ,, constantly ∣ "a" ∈ A)
g-map-iterate = g-map ∙ svar "f" ∙ (g-iterate ∙ var "f" γ ∙ svar "a")
                  ≡ᵇ
                g-iterate ∙ var "f" γ ∙ (svar "f" ∙ svar "a")

g-map-iterate-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-map-iterate-proof A =
  ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ]
  ∀-intro[ constantly ∣ "a" ∈ A ]
  pflöb "ih" equality-chain
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-map ∙ svar "f" ∙ (g-iterate ∙ var "f" γ ∙ svar "a")
      ≡ᵇ⟨ cong (g-map ∙ svar "f") (with-normalization tmlöb-β) ⟩
        g-map ∙ svar "f" ∙ (g-cons (svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)))
      ≡ᵇ⟨ ∀-elim later (∀[ later ∣ "s" ∈ GStream A ] g-map ∙ svar "f" ∙ (g-cons (svar "a") (svar "s")) ≡ᵇ g-cons (svar "f" ∙ svar "a") (g-map ∙ var "f" γ ∙ svar "s"))
           (∀-elim constantly (∀[ constantly ∣ "h" ∈ A ] ∀[ later ∣ "s" ∈ GStream A ]
                                  g-map ∙ svar "f" ∙ (g-cons (svar "h") (svar "s")) ≡ᵇ g-cons (svar "f" ∙ svar "h") (g-map ∙ var "f" γ ∙ svar "s"))
             (∀-elim constantly (∀[ constantly ∣ "f" ∈ A ⇛ A ] ∀[ constantly ∣ "h" ∈ A ] ∀[ later ∣ "s" ∈ GStream A ] g-map-cons)
               (g-map-cons-proof A)
               (svar "f"))
             (svar "a"))
           (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ))
        ⟩
        g-cons (svar "f" ∙ svar "a") (g-map ∙ var "f" γ ∙ (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)))
      ≡ᵇ⟨ g-cons-cong (svar "f" ∙ svar "a")
                      (svar "f" ∙ svar "a")
                      (g-map ∙ var "f" γ ∙ (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)))
                      (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
                      refl
                      (cong (g-map ∙ var "f" γ) (assumption' "ih" (id-cell {μ = later})))
        ⟩
        g-cons (svar "f" ∙ svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
      ≡ᵇ⟨ with-normalization tmlöb-β ⟨
        g-iterate ∙ var "f" γ ∙ (svar "f" ∙ svar "a") ∎

test-g-map-iterate : IsOk (check-proof ◇ (g-map-iterate-proof Nat') (∀[ constantly ∣ "f" ∈ Nat' ⇛ Nat' ] ∀[ constantly ∣ "a" ∈ Nat' ] g-map-iterate))
test-g-map-iterate = tt


g-iterate-iterate' : bProp (Γ ,, constantly ∣ "f" ∈ (A ⇛ A) ,, constantly ∣ "a" ∈ A)
g-iterate-iterate' = g-iterate ∙ var "f" γ ∙ svar "a"
                       ≡ᵇ
                     g-iterate' ∙ var "f" γ ∙ svar "a"

g-iterate-iterate'-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-iterate-iterate'-proof A =
  ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ] pflöb "ih" (∀-intro[ constantly ∣ "a" ∈ A ] equality-chain)
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-iterate ∙ var "f" γ ∙ svar "a"
      ≡ᵇ⟨ with-normalization tmlöb-β ⟩
        g-cons (svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ))
      ≡ᵇ⟨ g-cons-cong (svar "a") (svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)) (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
           refl (∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ svar "a") ≡ᵇ g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ svar "a"))
                   (∀-elim constantly (∀[ constantly ∣ "f" ∈ A ⇛ A ] ∀[ constantly ∣ "a" ∈ A ] g-map-iterate)
                     (g-map-iterate-proof A)
                     (var "f" γ))
                   (var "a" γ))
        ⟩
        g-cons (svar "a") (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
      ≡ᵇ⟨ g-cons-cong (svar "a") (svar "a") (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)) (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
            refl
            (∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-iterate ∙ var "f" δ ∙ svar "a" ≡ᵇ g-iterate' ∙ var "f" δ ∙ svar "a")
                    (assumption' "ih" (id-cell {μ = later}))
                    (var "f" γ ∙ var "a" γ))
        ⟩
        g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
      ≡ᵇ⟨ ∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-iterate' ∙ var "f" γ ∙ svar "a" ≡ᵇ g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
            (∀-elim constantly (∀[ constantly ∣ "f" ∈ A ⇛ A ] ∀[ constantly ∣ "a" ∈ A ] g-iterate'-cons)
              (g-iterate'-cons-proof A)
              (svar "f"))
            (svar "a")
        ⟨
        g-iterate' ∙ var "f" γ ∙ svar "a" ∎

test-g-iterate-iterate' : IsOk (check-proof ◇ (g-iterate-iterate'-proof Nat') (∀[ constantly ∣ "f" ∈ Nat' ⇛ Nat' ] ∀[ constantly ∣ "a" ∈ Nat' ] g-iterate-iterate'))
test-g-iterate-iterate' = tt
