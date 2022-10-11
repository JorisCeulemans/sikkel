module Experimental.LogicalFramework.MSTT.StreamTest where

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Named
open import Experimental.LogicalFramework.MSTT.BasicPrograms

private variable
  m n : Mode
  μ κ ρ : Modality m n
  Γ Δ : Ctx m
  T S A B C : Ty m


--------------------------------------------------
--------------------------------------------------
-- Definition of some helper functions and 2-cells that will be used
--   in the example programs with streams.

▻ : Ty ω → Ty ω
▻ T = ⟨ later ∣ T ⟩

-- If Γ ⊢ t : T, then Γ ⊢ next t : ▻ T.
-- Note that this is different from mod⟨ later ⟩ t, where t would be type-checked
--   in context Γ ,lock⟨ later ⟩.
next : Tm Γ T → Tm Γ (▻ T)
next t = coe[ 𝟙≤later ] triv t

-- If Γ ⊢ f : A ⇛ B and Γ ⊢ t : ▻ A, then Γ ⊢ f ⟨$-later⟩' t : ▻ B.
infixl 5 _⟨$-later⟩_
_⟨$-later⟩_ : Tm Γ (A ⇛ B) → Tm Γ (▻ A) → Tm Γ (▻ B)
f ⟨$-later⟩ t = next f ⊛ t

-- const⇒later∘const ∈ constantly ⇒ later ⓜ constantly
const⇒later∘const : TwoCell constantly (later ⓜ constantly)
const⇒later∘const = 𝟙≤later ⓣ-hor (id-cell {μ = constantly})

-- later⇒later∘later ∈ later ⇒ later ⓜ later
later⇒later∘later : TwoCell later (later ⓜ later)
later⇒later∘later = 𝟙≤later ⓣ-hor (id-cell {μ = later})


--------------------------------------------------
--------------------------------------------------
-- Examples involving guarded streams

open import Data.String

-- open import Relation.Binary.PropositionalEquality


--------------------------------------------------
-- The following is the example that is worked out in Section 3 of the MSFP submission.

-- Γ ⊢ g-map A B : ⟨ constantly ∣ A ⇛ B ⟩ ⇛ GStream A ⇛ GStream B

g-map : Tm Γ (⟨ constantly ∣ A ⇛ B ⟩ ⇛ GStream A ⇛ GStream B)
g-map {A = A} {B = B} =
  lam[ constantly ∣ "f" ∈ A ⇛ B ]
    (löb[later∣ "m" ∈ GStream A ⇛ GStream B ]
      (lam[ "s" ∈ GStream A ]
        let' mod⟨ constantly ⟩ "head-s" ← g-head (svar "s") in'
        let' mod⟨ later ⟩ "tail-s" ← g-tail (svar "s") in'
        g-cons (svar "f" ∙ svar "head-s")
               (svar "m" ∙ svar "tail-s")))

{-
g-map : TmExpr Γ (⟨ constantly ∣ A ⇛ B ⟩ ⇛ GStream A ⇛ GStream B)
g-map A B =
  lam[ constantly ∣ "f" ∈ A ⇛ B ]
    löb[later∣ "m" ∈ GStream A ⇛ GStream B ]
      lam[ "s" ∈ GStream A ]
        let' mod⟨ constantly ⟩ "head-s" ← g-head A ∙ svar "s" in'
        let' mod⟨ later ⟩ "tail-s" ← g-tail A ∙ svar "s" in' (
        g-cons B ∙⟨ constantly ⟩ (svar "f" ∙ svar "head-s")
                 ∙⟨ later ⟩ (svar "m" ∙ svar "tail-s"))

g-map-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Nat' ′⇛ ′Nat' ⟩ ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat')
g-map-sem = ⟦ g-map Nat' Nat' ⟧tm
-}

g-nats : Tm Γ (GStream Nat')
g-nats =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-cons zero
           (g-map ∙ (mod⟨ constantly ⟩ suc) ∙ svar "s")

{-
-- Γ ⊢ g-nats : GStream Nat'
g-nats : TmExpr ω
g-nats =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-consN ∙⟨ constantly ⟩ lit 0
            ∙⟨ later ⟩ (g-map Nat' Nat' ∙⟨ constantly ⟩ suc
                                        ∙ svar "s")

g-nats-sem : Tm ′◇ (′GStream ′Nat')
g-nats-sem = ⟦ g-nats ⟧tm


--------------------------------------------------
-- The follwing definitions are an implementation of all examples involving streams on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The Guarded Lambda-Calculus: Programming and Reasoning with Guarded Recursion for Coinductive Types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.
--   https://doi.org/10.2168/LMCS-12(3:7)2016

-}

g-head' : Tm Γ (GStream A ⇛ ⟨ constantly ∣ A ⟩)
g-head' = lam[ "s" ∈ GStream _ ] g-head (svar "s")

g-snd : Tm Γ (GStream A ⇛ ▻ ⟨ constantly ∣ A ⟩)
g-snd = lam[ "s" ∈ GStream _ ] (g-head' ⟨$-later⟩ g-tail (svar "s"))

{-

-- Γ ⊢ g-snd A : GStream A ⇛ ▻ ⟨ constantly ∣ A ⟩
g-snd : TyExpr ★ → TmExpr ω
g-snd A = lam[ "s" ∈ GStream A ] g-head A ⟨$-later⟩ (g-tail A ∙ svar "s")

g-snd-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ ′⟨ ′constantly ∣ ′Nat' ⟩)
g-snd-sem = ⟦ g-snd Nat' ⟧tm

-}

g-thrd : Tm Γ (GStream A ⇛ ▻ (▻ ⟨ constantly ∣ A ⟩))
g-thrd = lam[ "s" ∈ GStream _ ] (g-snd ⟨$-later⟩ g-tail (svar "s"))

{-
-- Γ ⊢ g-thrd A : GStream A ⇛ ▻ (▻ ⟨ constantly ∣ A ⟩)
g-thrd : TyExpr ★ → TmExpr ω
g-thrd A = lam[ "s" ∈ GStream A ] g-snd A ⟨$-later⟩ (g-tail A ∙ svar "s")

g-thrd-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′▻ ′⟨ ′constantly ∣ ′Bool' ⟩))
g-thrd-sem = ⟦ g-thrd Bool' ⟧tm

-}

g-zeros : Tm Γ (GStream Nat')
g-zeros =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-cons zero (svar "s")

{-
-- Γ ⊢ g-zeros : GStream Nat'
g-zeros : TmExpr ω
g-zeros =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-consN ∙⟨ constantly ⟩ lit 0
            ∙⟨ later ⟩ svar "s"

g-zeros-sem : Tm ′◇ (′GStream ′Nat')
g-zeros-sem = ⟦ g-zeros ⟧tm

-}

g-iterate' : Tm Γ (⟨ later ⓜ constantly ∣ A ⇛ A ⟩ ⇛ ⟨ constantly ∣ A ⟩ ⇛ GStream A)
g-iterate' {A = A} =
  lam[ later ⓜ constantly ∣ "f" ∈ A ⇛ A ]
    (löb[later∣ "g" ∈ ⟨ constantly ∣ A ⟩ ⇛ GStream A ]
      (lam[ constantly ∣ "x" ∈ A ]
        g-cons (svar "x") (svar "g" ∙ₘ (svar "f" ∙ var "x" const⇒later∘const))))

{-
-- Γ ⊢ g-iterate' A : ⟨ constantly | A ⇛ A ⟩ ⇛ ⟨ constantly ∣ A ⟩ ⇛ GStream A
g-iterate' : TyExpr ★ → TmExpr ω
g-iterate' A =
  lam[ later ⓜ constantly ∣ "f" ∈ A ⇛ A ]
    löb[later∣ "g" ∈ ⟨ constantly ∣ A ⟩ ⇛ GStream A ]
      lam[ constantly ∣ "x" ∈ A ]
        g-cons A ∙⟨ constantly ⟩ svar "x"
                 ∙⟨ later ⟩ (svar "g" ∙⟨ constantly ⟩ (svar "f" ∙ var "x" const⇒later∘const))

g-iterate'-sem : Tm ′◇ (′▻ ′⟨ ′constantly ∣ ′Nat' ′⇛ ′Nat' ⟩ ′⇛ ′⟨ ′constantly ∣ ′Nat' ⟩ ′⇛ ′GStream ′Nat')
g-iterate'-sem = ⟦ g-iterate' Nat' ⟧tm

-}

g-iterate : Tm Γ (⟨ later ⓜ constantly ∣ A ⇛ A ⟩ ⇛ ⟨ constantly ∣ A ⟩ ⇛ GStream A)
g-iterate {A = A} =
  lam[ later ⓜ constantly ∣ "f" ∈ A ⇛ A ]
    (lam[ constantly ∣ "a" ∈ A ]
      (löb[later∣ "s" ∈ GStream A ]
        g-cons (svar "a") (g-map ∙ₘ svar "f" ∙ svar "s")))

{-
-- This is a more general definition of iterate since the generating function of type
-- only has to be available later. The implementation itself applies g-map to
-- its corecursive call (represented by the variable "s"), which would not be allowed
-- in a definition of standard Agda streams by copattern matching.
-- Γ ⊢ g-iterate A : ⟨ later ⓜ constantly | A ⇛ A ⟩ ⇛ ⟨ constantly ∣ A ⟩ ⇛ GStream A
g-iterate : TyExpr ★ → TmExpr ω
g-iterate A =
  lam[ later ⓜ constantly ∣ "f" ∈ A ⇛ A ]
    lam[ constantly ∣ "a" ∈ A ]
      löb[later∣ "s" ∈ GStream A ]
        g-cons A ∙⟨ constantly ⟩ svar "a"
                 ∙⟨ later ⟩ (g-map A A ∙⟨ constantly ⟩ svar "f"
                                       ∙ svar "s")

g-iterate-sem : Tm ′◇ (′▻ ′⟨ ′constantly ∣ ′Bool' ′⇛ ′Bool' ⟩ ′⇛ ′⟨ ′constantly ∣ ′Bool' ⟩ ′⇛ ′GStream ′Bool')
g-iterate-sem = ⟦ g-iterate Bool' ⟧tm

-}

g-nats' : Tm Γ (GStream Nat')
g-nats' = g-iterate ∙ₘ suc ∙ₘ zero

{-
-- Γ ⊢ g-nats' : GStream Nat'
g-nats' : TmExpr ω
g-nats' = g-iterate Nat' ∙⟨ later ⓜ constantly ⟩ suc ∙⟨ constantly ⟩ lit 0

g-nats'-sem : Tm ′◇ (′GStream ′Nat')
g-nats'-sem = ⟦ g-nats' ⟧tm

-}

g-interleave : Tm Γ (GStream A ⇛ ▻ (GStream A) ⇛ GStream A)
g-interleave {A = A} =
  löb[later∣ "g" ∈ GStream A ⇛ ▻ (GStream A) ⇛ GStream A ]
    lam[ "s" ∈ GStream A ]
      (lam[ later ∣ "t" ∈ GStream A ]
        let' mod⟨ constantly ⟩ "head-s" ← g-head (svar "s") in'
        let' mod⟨ later ⟩ "tail-s" ← g-tail (svar "s") in'
        g-cons (svar "head-s")
               (svar "g" ∙ svar "t" ∙ next (svar "tail-s")))

{-
-- Γ ⊢ g-interleave A : GStream A ⇛ ▻ (GStream A) ⇛ GStream A
g-interleave : TyExpr ★ → TmExpr ω
g-interleave A =
  löb[later∣ "g" ∈ GStream A ⇛ ▻ (GStream A) ⇛ GStream A ]
    lam[ "s" ∈ GStream A ]
      lam[ later ∣ "t" ∈ GStream A ]
        let' mod⟨ constantly ⟩ "head-s" ← g-head A ∙ svar "s" in'
        let' mod⟨ later ⟩ "tail-s" ← g-tail A ∙ svar "s" in' (
        g-cons A ∙⟨ constantly ⟩ svar "head-s"
                 ∙⟨ later ⟩ (svar "g" ∙ svar "t" ∙ next (svar "tail-s")))

g-interleave-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat')
g-interleave-sem = ⟦ g-interleave Nat' ⟧tm

-}

g-toggle : Tm Γ (GStream Nat')
g-toggle =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-cons (suc ∙ zero) (g-cons zero (var "s" later⇒later∘later))

{-
-- Γ ⊢ g-toggle : GStream Nat'
g-toggle : TmExpr ω
g-toggle =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-consN ∙⟨ constantly ⟩ lit 1
            ∙⟨ later ⟩ (g-consN ∙⟨ constantly ⟩ lit 0
                                ∙⟨ later ⟩ var "s" later⇒later∘later)

g-toggle-sem : Tm ′◇ (′GStream ′Nat')
g-toggle-sem = ⟦ g-toggle ⟧tm

-}

g-paperfolds : Tm Γ (GStream Nat')
g-paperfolds =
  löb[later∣ "s" ∈ GStream Nat' ]
    (g-interleave ∙ g-toggle ∙ (mod⟨ later ⟩ svar "s"))

{-
-- Γ ⊢ g-paperfolds : GStream Nat'
g-paperfolds : TmExpr ω
g-paperfolds =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-interleave Nat' ∙ g-toggle
                      ∙ (mod⟨ later ⟩ svar "s")

g-paperfolds-sem : Tm ′◇ (′GStream ′Nat')
g-paperfolds-sem = ⟦ g-paperfolds ⟧tm

-}

g-initial : Tm Γ (((⟨ constantly ∣ A ⟩ ⊠ (▻ T)) ⇛ T) ⇛ GStream A ⇛ T)
g-initial {A = A} {T = T} =
  lam[ "f" ∈ (⟨ constantly ∣ A ⟩ ⊠ ▻ T) ⇛ T ]
    (löb[later∣ "g" ∈ GStream A ⇛ T ]
      (lam[ "s" ∈ GStream A ]
        (svar "f" ∙ pair (g-head (svar "s"))
                         ((mod⟨ later ⟩ svar "g") ⊛ g-tail (svar "s")))))

{-
-- GStream A is the initial algebra for the functor X ↦ ⟨ constantly ∣ A ⟩ ⊠ (▻ X).
-- Γ ⊢ g-initial : ((⟨ constantly ∣ A ⟩ ⊠ (▻ T)) ⇛ T) ⇛ GStream A ⇛ T
g-initial : TyExpr ★ → TyExpr ω → TmExpr ω
g-initial A T =
  lam[ "f" ∈ (⟨ constantly ∣ A ⟩ ⊠ ▻ T) ⇛ T ]
    löb[later∣ "g" ∈ GStream A ⇛ T ]
      lam[ "s" ∈ GStream A ]
        svar "f" ∙ (pair (g-head A ∙ svar "s")
                         ((mod⟨ later ⟩ svar "g") ⊛⟨ later ⟩ (g-tail A ∙ svar "s")))


g-initial-sem : Tm ′◇ (((′⟨ ′constantly ∣ ′Nat' ⟩ ′⊠ ′▻ ′Bool') ′⇛ ′Bool') ′⇛ ′GStream ′Nat' ′⇛ ′Bool')
g-initial-sem = ⟦ g-initial Nat' Bool' ⟧tm

-}

g-final : Tm Γ ((T ⇛ (⟨ constantly ∣ A ⟩ ⊠ (▻ T))) ⇛ T ⇛ GStream A)
g-final {T = T} {A = A} =
  lam[ "f" ∈ T ⇛ (⟨ constantly ∣ A ⟩ ⊠ ▻ T) ]
    (löb[later∣ "g" ∈ T ⇛ GStream A ]
      (lam[ "t" ∈ T ]
        let' mod⟨ constantly ⟩ "a" ← fst (svar "f" ∙ svar "t") in'
        let' mod⟨ later ⟩ "new-t" ← snd (svar "f" ∙ svar "t") in'
        g-cons (svar "a")
               (svar "g" ∙ svar "new-t")))

{-
-- GStream A is the final coalgebra for the functor X ↦ ⟨ constantly ∣ A ⟩ ⊠ (▻ X)
-- Γ ⊢ g-final : (T ⇛ (⟨ constantly ∣ A ⟩ ⊠ (▻ T))) ⇛ T ⇛ GStream A
g-final : TyExpr ★ → TyExpr ω → TmExpr ω
g-final A T =
  lam[ "f" ∈ T ⇛ (⟨ constantly ∣ A ⟩ ⊠ ▻ T) ]
    löb[later∣ "g" ∈ T ⇛ GStream A ]
      lam[ "t" ∈ T ]
        let' mod⟨ constantly ⟩ "a" ← fst (svar "f" ∙ svar "t") in'
        let' mod⟨ later ⟩ "new-t" ← snd (svar "f" ∙ svar "t") in'
        g-cons A ∙⟨ constantly ⟩ svar "a"
                 ∙⟨ later ⟩ (svar "g" ∙ svar "new-t")

g-final-sem : Tm ′◇ ((′Bool' ′⇛ (′⟨ ′constantly ∣ ′Nat' ⟩ ′⊠ ′▻ ′Bool')) ′⇛ ′Bool' ′⇛ ′GStream ′Nat')
g-final-sem = ⟦ g-final Nat' Bool' ⟧tm


--------------------------------------------------
-- Implementation of the examples on page 12 of the paper by Clouston et al. cited above.
-}

cst-bool : Tm Γ (⟨ constantly ∣ Bool' ⟩ ⇛ Bool')
cst-bool = lam[ constantly ∣ "b" ∈ Bool' ] (crisp-if ∙ₘ svar "b" ∙ (mod⟨ _ ⟩ true) ∙ (mod⟨ _ ⟩ false))
  where
    h : Tm Δ (Bool' ⇛ ⟨ forever ∣ Bool' ⟩ ⇛ ⟨ forever ∣ Bool' ⟩ ⇛ ⟨ forever ∣ Bool' ⟩)
    h = lam[ "b" ∈ Bool' ] (lam[ "t" ∈ _ ] (lam[ "f" ∈ _ ] if (svar "b") (svar "t") (svar "f")))

    crisp-if : Tm Δ (⟨ constantly ∣ Bool' ⟩ ⇛ ⟨ constantly ⓜ forever ∣ Bool' ⟩ ⇛ ⟨ constantly ⓜ forever ∣ Bool' ⟩ ⇛ Bool')
    crisp-if = lam[ constantly ∣ "b" ∈ Bool' ] (lam[ "t" ∈ _ ] (lam[ "f" ∈ _ ]
      triv⁻¹ (coe[ constantlyⓜforever≤𝟙 ] (comp ((mod⟨ constantly ⟩ (h ∙ svar "b")) ⊛ comp⁻¹ (svar "t") ⊛ comp⁻¹ (svar "f"))))))

g-thumorse : Tm Γ (GStream Bool')
g-thumorse =
  löb[later∣ "t-m" ∈ GStream Bool' ]
    let⟨ later ⟩ mod⟨ later ⟩ "s" ← g-tail (h ∙ svar "t-m") in'
    g-cons false (g-cons true (h ∙ svar "s"))
  where
    h : Tm Δ (GStream Bool' ⇛ GStream Bool')
    h =
      löb[later∣ "g" ∈ GStream Bool' ⇛ GStream Bool' ]
        (lam[ "s" ∈ GStream Bool' ]
          let' mod⟨ later ⟩ "new-tail" ← (mod⟨ later ⟩ svar "g") ⊛ g-tail (svar "s") in'
          if (cst-bool ∙ g-head (svar "s"))
             (g-cons true (g-cons false (var "new-tail" later⇒later∘later)))
             (g-cons false (g-cons true (var "new-tail" later⇒later∘later))))

{-
-- Γ ⊢ g-thumorse : GStream Bool'
g-thumorse : TmExpr ω
g-thumorse =
  löb[later∣ "t-m" ∈ GStream Bool' ]
    let⟨ later ⟩ mod⟨ later ⟩ "s" ← g-tailB ∙ (h ∙ svar "t-m") in'
    g-consB ∙⟨ constantly ⟩ false
            ∙⟨ later ⟩ (g-consB ∙⟨ constantly ⟩ true
                                ∙⟨ later ⟩ (h ∙ svar "s"))
  where
    -- Γ ⊢ h : GStream Bool' ⇛ GStream Bool'
    h : TmExpr ω
    h =
      löb[later∣ "g" ∈ GStream Bool' ⇛ GStream Bool' ]
        lam[ "s" ∈ GStream Bool' ]
          let' mod⟨ later ⟩ "new-tail" ← (mod⟨ later ⟩ svar "g") ⊛⟨ later ⟩ (g-tailB ∙ svar "s") in'
          constantly-if (g-headB ∙ svar "s")
                        (g-consB ∙⟨ constantly ⟩ true
                                 ∙⟨ later ⟩ (g-consB ∙⟨ constantly ⟩ false ∙⟨ later ⟩ var "new-tail" later⇒later∘later))
                        (g-consB ∙⟨ constantly ⟩ false
                                 ∙⟨ later ⟩ (g-consB ∙⟨ constantly ⟩ true ∙⟨ later ⟩ var "new-tail" later⇒later∘later))

g-thumorse-sem : Tm ′◇ (′GStream ′Bool')
g-thumorse-sem = ⟦ g-thumorse ⟧tm
-}

g-fibonacci-word : Tm Γ (GStream Bool')
g-fibonacci-word =
  löb[later∣ "fw" ∈ GStream Bool' ]
    let⟨ later ⟩ mod⟨ later ⟩ "s" ← g-tail (f ∙ svar "fw")
    in' g-cons false (g-cons true (f ∙ svar "s"))
  where
    f : Tm Δ (GStream Bool' ⇛ GStream Bool')
    f = löb[later∣ "g" ∈ GStream Bool' ⇛ GStream Bool' ]
          (lam[ "s" ∈ GStream Bool' ]
            let' mod⟨ later ⟩ "new-tail" ← (mod⟨ later ⟩ svar "g") ⊛ g-tail (svar "s") in'
            if (cst-bool ∙ g-head (svar "s"))
               (g-cons false (svar "new-tail"))
               (g-cons false (g-cons true (var "new-tail" later⇒later∘later))))

{-
-- Γ ⊢ g-fibonacci-word : GStream Bool'
g-fibonacci-word : TmExpr ω
g-fibonacci-word =
  löb[later∣ "fw" ∈ GStream Bool' ]
    let⟨ later ⟩ mod⟨ later ⟩ "s" ← g-tailB ∙ (f ∙ svar "fw") in'
    g-consB ∙⟨ constantly ⟩ false
            ∙⟨ later ⟩ (g-consB ∙⟨ constantly ⟩ true
                                ∙⟨ later ⟩ (f ∙ svar "s"))
  where
    -- Γ ⊢ f : GStream Bool' ⇛ GStream Bool'
    f : TmExpr ω
    f =
      löb[later∣ "g" ∈ GStream Bool' ⇛ GStream Bool' ]
        lam[ "s" ∈ GStream Bool' ]
          let' mod⟨ later ⟩ "new-tail" ← (mod⟨ later ⟩ svar "g") ⊛⟨ later ⟩ (g-tailB ∙ svar "s") in'
          constantly-if (g-headB ∙ svar "s")
                        (g-consB ∙⟨ constantly ⟩ false ∙⟨ later ⟩ svar "new-tail")
                        (g-consB ∙⟨ constantly ⟩ false ∙⟨ later ⟩ (
                                 g-consB ∙⟨ constantly ⟩ true ∙⟨ later ⟩ var "new-tail" later⇒later∘later))

g-fibonacci-word-sem : Tm ′◇ (′GStream ′Bool')
g-fibonacci-word-sem = ⟦ g-fibonacci-word ⟧tm


--------------------------------------------------
-- This is an implementation of an example from the end of section 1.1 of the paper
--   Robert Atkey, and Conor McBride.
--   Productive Coprogramming with Guarded Recursion.
--   ICFP 2013.
--   https://doi.org/10.1145/2544174.2500597
-}

g-mergef : Tm Γ ((⟨ constantly ∣ A ⟩ ⇛ ⟨ constantly ∣ B ⟩ ⇛ ▻ (GStream C) ⇛ GStream C) ⇛ GStream A ⇛ GStream B ⇛ GStream C)
g-mergef {A = A} {B} {C} =
  lam[ "f" ∈ ⟨ constantly ∣ A ⟩ ⇛ ⟨ constantly ∣ B ⟩ ⇛ ▻ (GStream C) ⇛ GStream C ]
    löb[later∣ "g" ∈ GStream A ⇛ GStream B ⇛ GStream C ]
      lam[ "xs" ∈ GStream A ]
        lam[ "ys" ∈ GStream B ]
          let' mod⟨ constantly ⟩ "head-xs" ← g-head (svar "xs") in'
          let' mod⟨ constantly ⟩ "head-ys" ← g-head (svar "ys") in'
          let' mod⟨ later ⟩ "tail-xs" ← g-tail (svar "xs") in'
          let' mod⟨ later ⟩ "tail-ys" ← g-tail (svar "ys") in'
          (svar "f" ∙ₘ svar "head-xs"
                    ∙ₘ svar "head-ys"
                    ∙ₘ (svar "g" ∙ svar "tail-xs" ∙ svar "tail-ys"))

{-
-- Γ ⊢ g-mergef A B C : (⟨ constantly ∣ A ⟩ ⇛ ⟨ constantly ∣ B ⟩ ⇛ ▻ (GStream C) ⇛ GStream C) ⇛ GStream A ⇛ GStream B ⇛ GStream C
g-mergef : (A B C : TyExpr ★) → TmExpr ω
g-mergef A B C =
  lam[ "f" ∈ ⟨ constantly ∣ A ⟩ ⇛ ⟨ constantly ∣ B ⟩ ⇛ ▻ (GStream C) ⇛ GStream C ]
    löb[later∣ "g" ∈ GStream A ⇛ GStream B ⇛ GStream C ]
      lam[ "xs" ∈ GStream A ]
        lam[ "ys" ∈ GStream B ]
          let' mod⟨ constantly ⟩ "head-xs" ← g-head A ∙ svar "xs" in'
          let' mod⟨ constantly ⟩ "head-ys" ← g-head B ∙ svar "ys" in'
          let' mod⟨ later ⟩ "tail-xs" ← g-tail A ∙ svar "xs" in'
          let' mod⟨ later ⟩ "tail-ys" ← g-tail B ∙ svar "ys" in'
          svar "f" ∙⟨ constantly ⟩ svar "head-xs"
                   ∙⟨ constantly ⟩ svar "head-ys"
                   ∙⟨ later ⟩ (svar "g" ∙ svar "tail-xs" ∙ svar "tail-ys")

g-mergef-sem : Tm ′◇ ((′⟨ ′constantly ∣ ′Nat' ⟩ ′⇛ ′⟨ ′constantly ∣ ′Bool' ⟩ ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Bool' ′⇛ ′GStream ′Nat')
g-mergef-sem = ⟦ g-mergef Nat' Bool' Nat' ⟧tm


--------------------------------------------------
-- Examples that are not taken from a specific paper
-}

g-zipWith : Tm Γ (⟨ constantly ∣ A ⇛ B ⇛ C ⟩ ⇛ GStream A ⇛ GStream B ⇛ GStream C)
g-zipWith {A = A} {B} {C} =
  lam[ constantly ∣ "f" ∈ A ⇛ B ⇛ C ]
    löb[later∣ "g" ∈ GStream A ⇛ GStream B ⇛ GStream C ]
      lam[ "as" ∈ GStream A ]
        lam[ "bs" ∈ GStream B ]
          let' mod⟨ constantly ⟩ "head-as" ← g-head (svar "as") in'
          let' mod⟨ constantly ⟩ "head-bs" ← g-head (svar "bs") in'
          let' mod⟨ later ⟩ "tail-as" ← g-tail (svar "as") in'
          let' mod⟨ later ⟩ "tail-bs" ← g-tail (svar "bs") in'
          g-cons (svar "f" ∙ svar "head-as" ∙ svar "head-bs")
                 (svar "g" ∙ svar "tail-as" ∙ svar "tail-bs")

{-
-- Γ ⊢ g-zipWith A B C : ⟨ constantly ∣ A ⇛ B ⇛ C ⟩ ⇛ GStream A ⇛ GStream B ⇛ GStream C
g-zipWith : (A B C : TyExpr ★) → TmExpr ω
g-zipWith A B C =
  lam[ constantly ∣ "f" ∈ A ⇛ B ⇛ C ]
    löb[later∣ "g" ∈ GStream A ⇛ GStream B ⇛ GStream C ]
      lam[ "as" ∈ GStream A ]
        lam[ "bs" ∈ GStream B ]
          let' mod⟨ constantly ⟩ "head-as" ← g-head A ∙ svar "as" in'
          let' mod⟨ constantly ⟩ "head-bs" ← g-head B ∙ svar "bs" in'
          let' mod⟨ later ⟩ "tail-as" ← g-tail A ∙ svar "as" in'
          let' mod⟨ later ⟩ "tail-bs" ← g-tail B ∙ svar "bs" in'
          g-cons C ∙⟨ constantly ⟩ (svar "f" ∙ svar "head-as" ∙ svar "head-bs")
                   ∙⟨ later ⟩ (svar "g" ∙ svar "tail-as" ∙ svar "tail-bs")

g-zipWith-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Bool' ′⇛ ′Nat' ′⇛ ′Bool' ⟩ ′⇛ ′GStream ′Bool' ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Bool')
g-zipWith-sem = ⟦ g-zipWith Bool' Nat' Bool' ⟧tm
-}

id : Tm Γ (T ⇛ T)
id {T = T} = lam[ "x" ∈ T ] svar "x"

plus : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
plus = nat-elim id (lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n"))))

g-fibs : Tm Γ (GStream Nat')
g-fibs =
  löb[later∣ "s" ∈ GStream Nat' ]
    let⟨ later ⟩ mod⟨ later ⟩ "tail-s" ← g-tail (svar "s") in'
    g-cons (suc ∙ zero)
           (g-cons (suc ∙ zero) (g-zipWith ∙ₘ plus ∙ var "s" later⇒later∘later ∙ svar "tail-s"))

{-
-- Γ ⊢ g-fibs : GStream Nat'
g-fibs : TmExpr ω
g-fibs =
  löb[later∣ "s" ∈ GStream Nat' ]
    let⟨ later ⟩ mod⟨ later ⟩ "tail-s" ← g-tailN ∙ svar "s" in'
    g-consN ∙⟨ constantly ⟩ lit 1
            ∙⟨ later ⟩ (g-consN ∙⟨ constantly ⟩ lit 1
                                ∙⟨ later ⟩ (g-zipWith Nat' Nat' Nat' ∙⟨ constantly ⟩ plus
                                                                     ∙ var "s" later⇒later∘later
                                                                     ∙ svar "tail-s"))

g-fibs-sem : Tm ′◇ (′GStream ′Nat')
g-fibs-sem = ⟦ g-fibs ⟧tm

-}

g-cons' : Tm Γ (⟨ constantly ∣ A ⟩ ⇛ ▻ (GStream A) ⇛ GStream A)
g-cons' {A = A} =
  lam[ constantly ∣ "a" ∈ A ] (lam[ later ∣ "s" ∈ GStream A ] g-cons (svar "a") (svar "s"))

g-tail' : Tm Γ (GStream A ⇛ ▻ (GStream A))
g-tail' = lam[ "s" ∈ GStream _ ] g-tail (svar "s")

g-flipFst : Tm Γ (GStream A ⇛ ▻ (GStream A))
g-flipFst {A = A} =
  lam[ "s" ∈ GStream A ]
    ((g-cons' ⟨$-later⟩ g-snd ∙ svar "s") ⊛ next (
    (g-cons' ⟨$-later⟩ next (g-head (svar "s"))) ⊛ (g-tail' ⟨$-later⟩ g-tail (svar "s"))))

{-
-- Γ ⊢ g-flipFst A : GStream A ⇛ ▻ (GStream A)
g-flipFst : TyExpr ★ → TmExpr ω
g-flipFst A =
  lam[ "s" ∈ GStream A ]
    g-cons A ⟨$-later⟩ g-snd A ∙ svar "s" ⊛⟨ later ⟩ next (
    g-cons A ⟨$-later⟩ next (g-head A ∙ svar "s") ⊛⟨ later ⟩ (g-tail A ⟨$-later⟩ g-tail A ∙ svar "s"))

g-flipFst-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′GStream ′Bool'))
g-flipFst-sem = ⟦ g-flipFst Bool' ⟧tm


--------------------------------------------------
--------------------------------------------------
-- Examples involving standard streams and the extraction
--   to Agda streams
-}
Stream' : Ty ★ → Ty ★
Stream' A = ⟨ forever ∣ GStream A ⟩


--------------------------------------------------
-- Continuation of the example worked out in Sections 3, 5 and 6 of the MSFP submission

-- Γ ⊢ nats : Stream' Nat'
nats : Tm Γ (Stream' Nat')
nats = mod⟨ forever ⟩ g-nats
{-
nats-sem : Tm ′◇ (′Stream' ′Nat')
nats-sem = ⟦ nats ⟧tm

nats-agda : Stream ℕ
nats-agda = extract-term nats-sem

nats-test : take 10 nats-agda ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
nats-test = refl


--------------------------------------------------
-- The following are implementations of all examples involving streams on page 11 of the paper
--   by Clouston et al. cited above.

-}

paperfolds : Tm Γ (Stream' Nat')
paperfolds = mod⟨ forever ⟩ g-paperfolds

{-
-- Γ ⊢ paperfolds : Stream' Nat'
paperfolds : TmExpr ★
paperfolds = mod⟨ forever ⟩ g-paperfolds

paperfolds-sem : Tm ′◇ (′Stream' ′Nat')
paperfolds-sem = ⟦ paperfolds ⟧tm

paperfolds-agda : Stream ℕ
paperfolds-agda = extract-term paperfolds-sem

paperfolds-test : take 10 paperfolds-agda ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
paperfolds-test = refl
-}

thue-morse : Tm Γ (Stream' Bool')
thue-morse = mod⟨ forever ⟩ g-thumorse

{-
-- Γ ⊢ thue-morse : Stream' Bool'
thue-morse : TmExpr ★
thue-morse = mod⟨ forever ⟩ g-thumorse

thue-morse-sem : Tm ′◇ (′Stream' ′Bool')
thue-morse-sem = ⟦ thue-morse ⟧tm

thue-morse-agda : Stream Bool
thue-morse-agda = extract-term thue-morse-sem

thue-morse-test : take 10 thue-morse-agda ≡ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ []
thue-morse-test = refl
-}

fibonacci-word : Tm Γ (Stream' Bool')
fibonacci-word = mod⟨ forever ⟩ g-fibonacci-word

{-
-- Γ ⊢ fibonacci-word : Stream' Bool'
fibonacci-word : TmExpr ★
fibonacci-word = mod⟨ forever ⟩ g-fibonacci-word

fibonacci-word-sem : Tm ′◇ (′Stream' ′Bool')
fibonacci-word-sem = ⟦ fibonacci-word ⟧tm

fibonacci-word-agda : Stream Bool
fibonacci-word-agda = extract-term fibonacci-word-sem

fibonacci-word-test : take 10 fibonacci-word-agda ≡ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ []
fibonacci-word-test = refl
-}

head' : Tm Γ (Stream' A ⇛ A)
head' =
  lam[ "s" ∈ Stream' _ ]
    triv⁻¹ (comp ((mod⟨ forever ⟩ (lam[ "x" ∈ _ ] g-head (svar "x"))) ⊛ svar "s"))

{-
-- Γ ⊢ head' A : Stream' A ⇛ A
head' : TyExpr ★ → TmExpr ★
head' A =
  lam[ "s" ∈ Stream' A ]
    triv⁻¹ (comp forever constantly
    ((mod⟨ forever ⟩ g-head A) ⊛⟨ forever ⟩ svar "s"))
-}

head-nats : {Γ : Ctx ★} → Tm Γ Nat'
head-nats = head' ∙ nats

{-
head-nats : TmExpr ★
head-nats = head' Nat' ∙ nats

head-nats-agda : ℕ
head-nats-agda = extract-term (⟦ head-nats ⟧tm)

head-nats-test : head-nats-agda ≡ 0
head-nats-test = refl
-}

tail' : Tm Γ (Stream' A ⇛ Stream' A)
tail' {A = A} =
  lam[ "s" ∈ Stream' A ] comp ((mod⟨ forever ⟩ g-tail') ⊛ svar "s")

{-
-- Γ ⊢ tail' A : Stream' A ⇛ Stream' A
-- Without the annotation, the inferred type would be
--   Stream' A ⇛ ⟨ forever ⓜ later ∣ GStream A ⟩
-- which is equal to the type given above since forever ⓜ later ≃ᵐ forever.
tail' : TyExpr ★ → TmExpr ★
tail' A = ann
  lam[ "s" ∈ Stream' A ]
    comp forever later ((mod⟨ forever ⟩ g-tail A) ⊛⟨ forever ⟩ svar "s")
  ∈ (Stream' A ⇛ Stream' A)

tailN-sem : Tm ′◇ (′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
tailN-sem = ⟦ tail' Nat' ⟧tm
-}

cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
cons' {A = A} = lam[ "a" ∈ A ] (lam[ forever ∣ "g-as" ∈ GStream A ]
  (mod⟨ forever ⟩ g-cons (svar "a") (svar "g-as")))

{-
-- Γ ⊢ cons' A : A ⇛ Stream' A ⇛ Stream' A
cons' : TyExpr ★ → TmExpr ★
cons' A = ann
  lam[ "a" ∈ A ] lam[ "as" ∈ Stream' A ]
    let' mod⟨ forever ⟩ "g-as" ← svar "as" in'
    (mod⟨ forever ⟩ g-cons A ∙⟨ constantly ⟩ svar "a"
                            ∙⟨ later ⟩ svar "g-as")
  ∈ (A ⇛ Stream' A ⇛ Stream' A)

consB-sem : Tm ′◇ (′Bool' ′⇛ ′Stream' ′Bool' ′⇛ ′Stream' ′Bool')
consB-sem = ⟦ cons' Bool' ⟧tm
-}

map' : Tm Γ ((A ⇛ B) ⇛ Stream' A ⇛ Stream' B)
map' {A = A} {B = B} =
  lam[ "f" ∈ A ⇛ B ]
    (lam[ forever ∣ "g-s" ∈ GStream A ]
      (mod⟨ forever ⟩ (g-map ∙ₘ svar "f" ∙ svar "g-s")))

{-
-- Γ ⊢ map' A B : (A ⇛ B) ⇛ Stream' A ⇛ Stream' B
map' : TyExpr ★ → TyExpr ★ → TmExpr ★
map' A B =
  lam[ "f" ∈ A ⇛ B ]
    lam[ "s" ∈ Stream' A ]
      let' mod⟨ forever ⟩ "g-s" ← svar "s" in'
      (mod⟨ forever ⟩ g-map A B ∙⟨ constantly ⟩ svar "f"
                                ∙ svar "g-s")

map'-sem : Tm ′◇ ((′Nat' ′⇛ ′Nat') ′⇛ ′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
map'-sem = ⟦ map' Nat' Nat' ⟧tm
-}

g-every2nd : Tm Γ (⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A)
g-every2nd {A = A} =
  löb[later∣ "g" ∈ ⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A ]
    (lam[ constantly ∣ "s" ∈ Stream' A ]
      g-cons (head' ∙ svar "s")
             (svar "g" ∙ₘ (tail' ∙ (tail' ∙ var "s" const⇒later∘const))))

{-
-- Γ ⊢ g-every2nd A : ⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A
g-every2nd : TyExpr ★ → TmExpr ω
g-every2nd A =
  löb[later∣ "g" ∈ ⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A ]
    lam[ constantly ∣ "s" ∈ Stream' A ]
      g-cons A ∙⟨ constantly ⟩ (head' A ∙ svar "s")
               ∙⟨ later ⟩ (svar "g" ∙⟨ constantly ⟩ (tail' A ∙ (tail' A ∙ var "s" const⇒later∘const)))

g-every2ndB-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Stream' ′Bool' ⟩ ′⇛ ′GStream ′Bool')
g-every2ndB-sem = ⟦ g-every2nd Bool' ⟧tm
-}

every2nd : Tm Γ (Stream' A ⇛ Stream' A)
every2nd {A = A} =
  lam[ "s" ∈ Stream' A ]
    (mod⟨ forever ⟩ (g-every2nd ∙ₘ svar "s"))

{-
-- Γ ⊢ every2nd A : Stream' A ⇛ Stream' A
every2nd : TyExpr ★ → TmExpr ★
every2nd A =
  lam[ "s" ∈ Stream' A ]
    mod⟨ forever ⟩ (g-every2nd A ∙⟨ constantly ⟩ svar "s")

every2ndN-sem : Tm ′◇ (′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
every2ndN-sem = ⟦ every2nd Nat' ⟧tm

every2nd-test : take 6 (extract-term (every2ndN-sem $ nats-sem))
                ≡ 0 ∷ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ []
every2nd-test = refl
-}

g-diag : Tm Γ (⟨ constantly ∣ Stream' (Stream' A) ⟩ ⇛ GStream A)
g-diag {A = A} =
  löb[later∣ "g" ∈ ⟨ constantly ∣ Stream' (Stream' A) ⟩ ⇛ GStream A ]
    (lam[ constantly ∣ "xss" ∈ Stream' (Stream' A) ]
      g-cons (head' ∙ (head' ∙ svar "xss"))
             (svar "g" ∙ₘ (map' ∙ tail' ∙ var "xss" const⇒later∘const)))

{-
-- Γ ⊢ g-diag : ⟨ constantly ∣ Stream' (Stream' A) ⟩ ⇛ GStream A
g-diag : TyExpr ★ → TmExpr ω
g-diag A =
  löb[later∣ "g" ∈ ⟨ constantly ∣ Stream' (Stream' A) ⟩ ⇛ GStream A ]
    lam[ constantly ∣ "xss" ∈ Stream' (Stream' A) ]
      g-cons A ∙⟨ constantly ⟩ (head' A ∙ (head' (Stream' A) ∙ svar "xss"))
               ∙⟨ later ⟩ (svar "g" ∙⟨ constantly ⟩ (map' (Stream' A) (Stream' A) ∙ tail' A
                                                                                  ∙ (tail' (Stream' A) ∙ var "xss" const⇒later∘const)))

g-diagB-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Stream' (′Stream' ′Bool') ⟩ ′⇛ ′GStream ′Bool')
g-diagB-sem = ⟦ g-diag Bool' ⟧tm
-}

diag : Tm Γ (Stream' (Stream' A) ⇛ Stream' A)
diag {A = A} =
  lam[ "s" ∈ Stream' (Stream' A) ]
    (mod⟨ forever ⟩ (g-diag ∙ₘ svar "s"))

{-
-- Γ ⊢ diag : Stream' (Stream' A) ⇛ Stream' A
diag : TyExpr ★ → TmExpr ★
diag A =
  lam[ "s" ∈ Stream' (Stream' A) ]
    mod⟨ forever ⟩ (g-diag A ∙⟨ constantly ⟩ svar "s")

diagB-sem : Tm ′◇ (′Stream' (′Stream' ′Bool') ′⇛ ′Stream' ′Bool')
diagB-sem = ⟦ diag Bool' ⟧tm


--------------------------------------------------
-- Example not taken from a paper
-}

fibs : Tm Γ (Stream' Nat')
fibs = mod⟨ forever ⟩ g-fibs

{-
-- Γ ⊢ fibs : Stream' Nat'
fibs : TmExpr ★
fibs = mod⟨ forever ⟩ g-fibs

fibs-sem : Tm ′◇ (′Stream' ′Nat')
fibs-sem = ⟦ fibs ⟧tm

fibs-agda : Stream ℕ
fibs-agda = extract-term fibs-sem

fibs-test : take 10 fibs-agda ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
fibs-test = refl
-}
