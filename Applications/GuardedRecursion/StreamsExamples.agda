--------------------------------------------------
-- Many example programs dealing with streams (guarded and standard)
--------------------------------------------------

module Applications.GuardedRecursion.StreamsExamples where

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (take; head; tail)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure renaming (◇ to ′◇) hiding (_⇒_)
open import Model.Modality renaming (⟨_∣_⟩ to ′⟨_∣_⟩) using ()
open import Model.Type.Constant renaming (Nat' to ′Nat'; Bool' to ′Bool')
open import Model.Type.Function hiding (lam; lam[_∈_]_) renaming (_⇛_ to _′⇛_)
open import Model.Type.Product hiding (pair; fst; snd) renaming (_⊠_ to _′⊠_)
open import Applications.GuardedRecursion.Model.Modalities
  hiding (next; löb; lift▻; lift2▻; 𝟙≤later) renaming (▻ to ′▻; constantly to ′constantly; forever to ′forever; later to ′later)
open import Applications.GuardedRecursion.Model.Streams.Guarded hiding (g-cons; g-head; g-tail) renaming (GStream to ′GStream)
open import Applications.GuardedRecursion.Model.Streams.Standard renaming (Stream' to ′Stream')
open import Extraction

open import Applications.GuardedRecursion.MSTT


--------------------------------------------------
--------------------------------------------------
-- Abbreviations for frequently used combinations

g-consN = g-cons Nat'
g-headN = g-head Nat'
g-tailN = g-tail Nat'

g-consB = g-cons Bool'
g-headB = g-head Bool'
g-tailB = g-tail Bool'


--------------------------------------------------
--------------------------------------------------
-- Definition of some helper functions and 2-cells that will be used
--   in the example programs with streams.

-- If Γ ⊢ t : T, then Γ ⊢ next t : ▻ T.
-- Note that this is different from mod⟨ later ⟩ t, where t would be type-checked
--   in context Γ ,lock⟨ later ⟩.
next : TmExpr ω → TmExpr ω
next t = coe[ 𝟙≤later ∈ 𝟙 ⇒ later ] triv t

-- If Γ ⊢ f : A ⇛ B and Γ ⊢ t : ▻ A, then Γ ⊢ f ⟨$-later⟩' t : ▻ B.
infixl 5 _⟨$-later⟩_
_⟨$-later⟩_ : TmExpr ω → TmExpr ω → TmExpr ω
f ⟨$-later⟩ t = next f ⊛⟨ later ⟩ t

-- const⇒later∘const ∈ constantly ⇒ later ⓜ constantly
const⇒later∘const : TwoCellExpr
const⇒later∘const = 𝟙≤later ⓣ-hor (ann id-cell ∈ constantly ⇒ constantly)

-- later⇒later∘later ∈ later ⇒ later ⓜ later
later⇒later∘later : TwoCellExpr
later⇒later∘later = 𝟙≤later ⓣ-hor (ann id-cell ∈ later ⇒ later)


--------------------------------------------------
--------------------------------------------------
-- Examples involving guarded streams

--------------------------------------------------
-- The following is the example that is worked out in Section 3 of the MSFP submission.

-- Γ ⊢ g-map A B : ⟨ constantly ∣ A ⇛ B ⟩ ⇛ GStream A ⇛ GStream B
g-map : TyExpr ★ → TyExpr ★ → TmExpr ω
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

-- Γ ⊢ g-snd A : GStream A ⇛ ▻ ⟨ constantly ∣ A ⟩
g-snd : TyExpr ★ → TmExpr ω
g-snd A = lam[ "s" ∈ GStream A ] g-head A ⟨$-later⟩ (g-tail A ∙ svar "s")

g-snd-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ ′⟨ ′constantly ∣ ′Nat' ⟩)
g-snd-sem = ⟦ g-snd Nat' ⟧tm

-- Γ ⊢ g-thrd A : GStream A ⇛ ▻ (▻ ⟨ constantly ∣ A ⟩)
g-thrd : TyExpr ★ → TmExpr ω
g-thrd A = lam[ "s" ∈ GStream A ] g-snd A ⟨$-later⟩ (g-tail A ∙ svar "s")

g-thrd-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′▻ ′⟨ ′constantly ∣ ′Bool' ⟩))
g-thrd-sem = ⟦ g-thrd Bool' ⟧tm

-- Γ ⊢ g-zeros : GStream Nat'
g-zeros : TmExpr ω
g-zeros =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-consN ∙⟨ constantly ⟩ lit 0
            ∙⟨ later ⟩ svar "s"

g-zeros-sem : Tm ′◇ (′GStream ′Nat')
g-zeros-sem = ⟦ g-zeros ⟧tm

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

-- Γ ⊢ g-nats' : GStream Nat'
g-nats' : TmExpr ω
g-nats' = g-iterate Nat' ∙⟨ later ⓜ constantly ⟩ suc ∙⟨ constantly ⟩ lit 0

g-nats'-sem : Tm ′◇ (′GStream ′Nat')
g-nats'-sem = ⟦ g-nats' ⟧tm

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

-- Γ ⊢ g-toggle : GStream Nat'
g-toggle : TmExpr ω
g-toggle =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-consN ∙⟨ constantly ⟩ lit 1
            ∙⟨ later ⟩ (g-consN ∙⟨ constantly ⟩ lit 0
                                ∙⟨ later ⟩ var "s" later⇒later∘later)

g-toggle-sem : Tm ′◇ (′GStream ′Nat')
g-toggle-sem = ⟦ g-toggle ⟧tm

-- Γ ⊢ g-paperfolds : GStream Nat'
g-paperfolds : TmExpr ω
g-paperfolds =
  löb[later∣ "s" ∈ GStream Nat' ]
    g-interleave Nat' ∙ g-toggle
                      ∙ (mod⟨ later ⟩ svar "s")

g-paperfolds-sem : Tm ′◇ (′GStream ′Nat')
g-paperfolds-sem = ⟦ g-paperfolds ⟧tm

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

Stream' : TyExpr ★ → TyExpr ★
Stream' A = ⟨ forever ∣ GStream A ⟩


--------------------------------------------------
-- Continuation of the example worked out in Sections 3, 5 and 6 of the MSFP submission

-- Γ ⊢ nats : Stream' Nat'
nats : TmExpr ★
nats = mod⟨ forever ⟩ g-nats

nats-sem : Tm ′◇ (′Stream' ′Nat')
nats-sem = ⟦ nats ⟧tm

nats-agda : Stream ℕ
nats-agda = extract-term nats-sem

nats-test : take 10 nats-agda ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
nats-test = refl


--------------------------------------------------
-- The following are implementations of all examples involving streams on page 11 of the paper
--   by Clouston et al. cited above.

-- Γ ⊢ paperfolds : Stream' Nat'
paperfolds : TmExpr ★
paperfolds = mod⟨ forever ⟩ g-paperfolds

paperfolds-sem : Tm ′◇ (′Stream' ′Nat')
paperfolds-sem = ⟦ paperfolds ⟧tm

paperfolds-agda : Stream ℕ
paperfolds-agda = extract-term paperfolds-sem

paperfolds-test : take 10 paperfolds-agda ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
paperfolds-test = refl

-- Γ ⊢ thue-morse : Stream' Bool'
thue-morse : TmExpr ★
thue-morse = mod⟨ forever ⟩ g-thumorse

thue-morse-sem : Tm ′◇ (′Stream' ′Bool')
thue-morse-sem = ⟦ thue-morse ⟧tm

thue-morse-agda : Stream Bool
thue-morse-agda = extract-term thue-morse-sem

thue-morse-test : take 10 thue-morse-agda ≡ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ []
thue-morse-test = refl

-- Γ ⊢ fibonacci-word : Stream' Bool'
fibonacci-word : TmExpr ★
fibonacci-word = mod⟨ forever ⟩ g-fibonacci-word

fibonacci-word-sem : Tm ′◇ (′Stream' ′Bool')
fibonacci-word-sem = ⟦ fibonacci-word ⟧tm

fibonacci-word-agda : Stream Bool
fibonacci-word-agda = extract-term fibonacci-word-sem

fibonacci-word-test : take 10 fibonacci-word-agda ≡ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ []
fibonacci-word-test = refl

-- Γ ⊢ head' A : Stream' A ⇛ A
head' : TyExpr ★ → TmExpr ★
head' A =
  lam[ "s" ∈ Stream' A ]
    triv⁻¹ (comp forever constantly
    ((mod⟨ forever ⟩ g-head A) ⊛⟨ forever ⟩ svar "s"))

head-nats : TmExpr ★
head-nats = head' Nat' ∙ nats

head-nats-agda : ℕ
head-nats-agda = extract-term (⟦ head-nats ⟧tm)

head-nats-test : head-nats-agda ≡ 0
head-nats-test = refl

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

-- Γ ⊢ g-every2nd A : ⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A
g-every2nd : TyExpr ★ → TmExpr ω
g-every2nd A =
  löb[later∣ "g" ∈ ⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A ]
    lam[ constantly ∣ "s" ∈ Stream' A ]
      g-cons A ∙⟨ constantly ⟩ (head' A ∙ svar "s")
               ∙⟨ later ⟩ (svar "g" ∙⟨ constantly ⟩ (tail' A ∙ (tail' A ∙ var "s" const⇒later∘const)))

g-every2ndB-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Stream' ′Bool' ⟩ ′⇛ ′GStream ′Bool')
g-every2ndB-sem = ⟦ g-every2nd Bool' ⟧tm

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

-- Γ ⊢ diag : Stream' (Stream' A) ⇛ Stream' A
diag : TyExpr ★ → TmExpr ★
diag A =
  lam[ "s" ∈ Stream' (Stream' A) ]
    mod⟨ forever ⟩ (g-diag A ∙⟨ constantly ⟩ svar "s")

diagB-sem : Tm ′◇ (′Stream' (′Stream' ′Bool') ′⇛ ′Stream' ′Bool')
diagB-sem = ⟦ diag Bool' ⟧tm


--------------------------------------------------
-- Example not taken from a paper

-- Γ ⊢ fibs : Stream' Nat'
fibs : TmExpr ★
fibs = mod⟨ forever ⟩ g-fibs

fibs-sem : Tm ′◇ (′Stream' ′Nat')
fibs-sem = ⟦ fibs ⟧tm

fibs-agda : Stream ℕ
fibs-agda = extract-term fibs-sem

fibs-test : take 10 fibs-agda ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
fibs-test = refl
