--------------------------------------------------
-- Many example programs dealing with streams (guarded and standard)
--------------------------------------------------

module Applications.GuardedRecursion.StreamsExamples where

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (take; head; tail)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure renaming (◇ to ′◇)
open import Model.Modality renaming (⟨_∣_⟩ to ′⟨_∣_⟩) using ()
open import Model.Type.Discrete renaming (Nat' to ′Nat'; Bool' to ′Bool')
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
-- Definition of some helper functions that are used a lot
--   in the example programs with streams.

-- If Γ ⊢ f : ⟨ μ ∣ A ⇛ B ⟩ and Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ f ⊛⟨ μ ⟩ t : ⟨ μ ∣ B ⟩.
infixl 5 _⊛⟨_⟩_
_⊛⟨_⟩_ : ∀ {m m'} → TmExpr m → ModalityExpr m' m → TmExpr m → TmExpr m
f ⊛⟨ μ ⟩ t = mod-intro μ (mod-elim μ f ∙ mod-elim μ t)

-- If Γ ,lock⟨ μ ⟩ ⊢ f : A ⇛ B and Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ f ⟨$- μ ⟩ t : ⟨ μ ∣ B ⟩.
infixl 5 _⟨$-_⟩_
_⟨$-_⟩_ : ∀ {m m'} → TmExpr m' → ModalityExpr m' m → TmExpr m → TmExpr m
f ⟨$- μ ⟩ t = mod-intro μ (f ∙ mod-elim μ t)

-- If Γ ⊢ t : T, then Γ ⊢ next t : ▻ T.
-- Note that this is different from (mod-intro later t), where t would be type-checked
--   in context Γ ,lock⟨ later ⟩.
next : TmExpr ω → TmExpr ω
next t = coe[ 𝟙≤later ∈ 𝟙 ⇒ later ] mod-intro 𝟙 t

-- If Γ ⊢ f : A ⇛ B and Γ ⊢ t : ▻ A, then Γ ⊢ f ⟨$-later⟩' t : ▻ B.
-- The difference with f ⟨$- later ⟩ t is that f is type-checked in Γ and not Γ ,lock⟨ later ⟩.
infixl 5 _⟨$-later⟩'_
_⟨$-later⟩'_ : TmExpr ω → TmExpr ω → TmExpr ω
f ⟨$-later⟩' t = next f ⊛⟨ later ⟩ t

-- Γ ⊢ lift▻ T S : (T ⇛ S) ⇛ ▻ T ⇛ ▻ S.
lift▻ : TyExpr ω → TyExpr ω → TmExpr ω
lift▻ T S = lam[ "f" ∈ T ⇛ S ] lam[ "t" ∈ ▻ T ] (var "f" ⟨$-later⟩' var "t")

-- Γ ⊢ lift2▻ T S R : (T ⇛ S ⇛ R) ⇛ ▻ T ⇛ ▻ S ⇛ ▻ R.
lift2▻ : TyExpr ω → TyExpr ω → TyExpr ω → TmExpr ω
lift2▻ T S R =
  lam[ "f" ∈ T ⇛ S ⇛ R ] lam[ "t" ∈ ▻ T ] lam[ "s" ∈ ▻ S ] (var "f" ⟨$-later⟩' var "t" ⊛⟨ later ⟩ var "s")


--------------------------------------------------
--------------------------------------------------
-- Examples involving guarded streams

--------------------------------------------------
-- The following is the example that is worked out in Section 3 of the CPP submission.

-- Γ ⊢ g-map A B : ⟨ constantly ∣ A ⇛ B ⟩ ⇛ GStream A ⇛ GStream B
g-map : TyExpr ★ → TyExpr ★ → TmExpr ω
g-map A B =
  lam[ "f" ∈ ⟨ constantly ∣ A ⇛ B ⟩ ]
    löb[ "m" ∈▻ (GStream A ⇛ GStream B) ]
      lam[ "s" ∈ GStream A ]
        g-cons B ∙ (var "f" ⊛⟨ constantly ⟩ g-head A ∙ var "s")
                 ∙ (var "m" ⊛⟨ later ⟩ g-tail A ∙ var "s")

g-map-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Nat' ′⇛ ′Nat' ⟩ ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat')
g-map-sem = ⟦ g-map Nat' Nat' ⟧tm

-- Γ ⊢ g-nats : GStream Nat'
g-nats : TmExpr ω
g-nats =
  löb[ "s" ∈▻ (GStream Nat') ]
    g-consN ∙ mod-intro constantly (lit 0)
            ∙ (g-map Nat' Nat' ∙ mod-intro constantly suc ⟨$-later⟩' var "s")

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
g-snd A = lam[ "s" ∈ GStream A ] g-head A ⟨$-later⟩' g-tail A ∙ var "s"

g-snd-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ ′⟨ ′constantly ∣ ′Nat' ⟩)
g-snd-sem = ⟦ g-snd Nat' ⟧tm

-- Γ ⊢ g-thrd A : GStream A ⇛ ▻ (▻ ⟨ constantly ∣ A ⟩)
g-thrd : TyExpr ★ → TmExpr ω
g-thrd A = lam[ "s" ∈ GStream A ] g-snd A ⟨$-later⟩' g-tail A ∙ var "s"

g-thrd-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′▻ ′⟨ ′constantly ∣ ′Bool' ⟩))
g-thrd-sem = ⟦ g-thrd Bool' ⟧tm

-- Γ ⊢ g-zeros : GStream Nat'
g-zeros : TmExpr ω
g-zeros = löb[ "s" ∈▻ (GStream Nat') ] g-consN ∙ mod-intro constantly (lit 0) ∙ var "s"

g-zeros-sem : Tm ′◇ (′GStream ′Nat')
g-zeros-sem = ⟦ g-zeros ⟧tm

-- Γ ⊢ g-iterate' A : ⟨ constantly | A ⇛ A ⟩ ⇛ ⟨ constantly ∣ A ⟩ ⇛ GStream A
g-iterate' : TyExpr ★ → TmExpr ω
g-iterate' A =
  lam[ "f" ∈ ⟨ constantly ∣ A ⇛ A ⟩ ]
    löb[ "g" ∈▻ (⟨ constantly ∣ A ⟩ ⇛ GStream A) ]
      lam[ "x" ∈ ⟨ constantly ∣ A ⟩ ]
        g-cons A ∙ var "x"
                 ∙ (var "g" ⊛⟨ later ⟩ (next (var "f" ⊛⟨ constantly ⟩ var "x")))

g-iterate'-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Nat' ′⇛ ′Nat' ⟩ ′⇛ ′⟨ ′constantly ∣ ′Nat' ⟩ ′⇛ ′GStream ′Nat')
g-iterate'-sem = ⟦ g-iterate' Nat' ⟧tm

-- This is a more general definition of iterate since the generating function of type
-- ⟨ constantly ∣ A ⇛ A ⟩ appears under ▻. The implementation itself applies g-map to
-- its corecursive call (represented by the variable "s"), which would not be allowed
-- in a definition of standard Agda streams by copattern matching.
-- Γ ⊢ g-iterate A : ⟨ constantly | A ⇛ A ⟩ ⇛ ⟨ constantly ∣ A ⟩ ⇛ GStream A
g-iterate : TyExpr ★ → TmExpr ω
g-iterate A =
  lam[ "f" ∈ ▻ ⟨ constantly ∣ A ⇛ A ⟩ ]
    lam[ "a" ∈ ⟨ constantly ∣ A ⟩ ]
      löb[ "s" ∈▻ (GStream A) ]
        g-cons A ∙ var "a"
                 ∙ (g-map A A ⟨$-later⟩' var "f" ⊛⟨ later ⟩ var "s")

g-iterate-sem : Tm ′◇ (′▻ ′⟨ ′constantly ∣ ′Bool' ′⇛ ′Bool' ⟩ ′⇛ ′⟨ ′constantly ∣ ′Bool' ⟩ ′⇛ ′GStream ′Bool')
g-iterate-sem = ⟦ g-iterate Bool' ⟧tm

-- Γ ⊢ g-nats' : GStream Nat'
g-nats' : TmExpr ω
g-nats' = g-iterate Nat' ∙ next (mod-intro constantly suc) ∙ mod-intro constantly (lit 0)

g-nats'-sem : Tm ′◇ (′GStream ′Nat')
g-nats'-sem = ⟦ g-nats' ⟧tm

-- Γ ⊢ g-interleave A : GStream A ⇛ ▻ (GStream A) ⇛ GStream A
g-interleave : TyExpr ★ → TmExpr ω
g-interleave A =
  löb[ "g" ∈▻ (GStream A ⇛ ▻ (GStream A) ⇛ GStream A) ]
    lam[ "s" ∈ GStream A ]
      lam[ "t" ∈ ▻ (GStream A) ]
        g-cons A ∙ (g-head A ∙ var "s")
                 ∙ (var "g" ⊛⟨ later ⟩ var "t" ⊛⟨ later ⟩ next (g-tail A ∙ var "s"))

g-interleave-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat')
g-interleave-sem = ⟦ g-interleave Nat' ⟧tm

-- Γ ⊢ g-toggle : GStream Nat'
g-toggle : TmExpr ω
g-toggle = löb[ "s" ∈▻ (GStream Nat') ]
             g-consN ∙ (mod-intro constantly (lit 1))
                     ∙ (next (g-consN ∙ mod-intro constantly (lit 0) ∙ var "s"))

g-toggle-sem : Tm ′◇ (′GStream ′Nat')
g-toggle-sem = ⟦ g-toggle ⟧tm

-- Γ ⊢ g-paperfolds : GStream Nat'
g-paperfolds : TmExpr ω
g-paperfolds = löb[ "s" ∈▻ (GStream Nat') ] g-interleave Nat' ∙ g-toggle ∙ var "s"

g-paperfolds-sem : Tm ′◇ (′GStream ′Nat')
g-paperfolds-sem = ⟦ g-paperfolds ⟧tm

-- Γ ⊢ g-initial : ((⟨ constantly ∣ A ⟩ ⊠ (▻ T)) ⇛ T) ⇛ GStream A ⇛ T
g-initial : TyExpr ★ → TyExpr ω → TmExpr ω
g-initial A T =
  löb[ "g" ∈▻ (((⟨ constantly ∣ A ⟩ ⊠ (▻ T)) ⇛ T) ⇛ GStream A ⇛ T) ]
    lam[ "f" ∈ (⟨ constantly ∣ A ⟩ ⊠ (▻ T)) ⇛ T ]
      lam[ "s" ∈ GStream A ]
        var "f" ∙ (pair (g-head A ∙ (var "s"))
                        (var "g" ⊛⟨ later ⟩ next (var "f") ⊛⟨ later ⟩ g-tail A ∙ var "s"))

g-initial-sem : Tm ′◇ (((′⟨ ′constantly ∣ ′Nat' ⟩ ′⊠ ′▻ ′Bool') ′⇛ ′Bool') ′⇛ ′GStream ′Nat' ′⇛ ′Bool')
g-initial-sem = ⟦ g-initial Nat' Bool' ⟧tm

-- Γ ⊢ g-final : (T ⇛ (⟨ constantly ∣ A ⟩ ⊠ (▻ T))) ⇛ T ⇛ GStream A
g-final : TyExpr ★ → TyExpr ω → TmExpr ω
g-final A T =
  löb[ "g" ∈▻ ((T ⇛ (⟨ constantly ∣ A ⟩ ⊠ (▻ T))) ⇛ T ⇛ GStream A) ]
    lam[ "f" ∈ T ⇛ (⟨ constantly ∣ A ⟩ ⊠ (▻ T)) ]
      lam[ "x" ∈ T ]
        g-cons A ∙ (fst (var "f" ∙ var "x"))
                 ∙ (var "g" ⊛⟨ later ⟩ next (var "f") ⊛⟨ later ⟩ snd (var "f" ∙ var "x"))

g-final-sem : Tm ′◇ ((′Bool' ′⇛ (′⟨ ′constantly ∣ ′Nat' ⟩ ′⊠ ′▻ ′Bool')) ′⇛ ′Bool' ′⇛ ′GStream ′Nat')
g-final-sem = ⟦ g-final Nat' Bool' ⟧tm


--------------------------------------------------
-- Implementation of the examples on page 12 of the paper by Clouston et al. cited above.

-- Γ ⊢ g-thumorse : GStream Bool'
g-thumorse : TmExpr ω
g-thumorse =
  let liftSB▻ = lift▻ (GStream Bool') (GStream Bool')
      liftLSB▻ = lift▻ (▻ (GStream Bool')) (▻ (GStream Bool'))
  in
  löb[ "t-m" ∈▻ (GStream Bool') ]
    g-consB ∙ mod-intro constantly false
            ∙ (g-consB ∙ (mod-intro constantly true)
                       ⟨$-later⟩' (liftLSB▻ ∙ (liftSB▻ ∙ h)) ∙
                            (g-tailB ⟨$-later⟩' liftSB▻ ∙ h ∙ var "t-m"))
  where
    h : TmExpr ω
    h =
      löb[ "g" ∈▻ (GStream Bool' ⇛ GStream Bool') ]
        lam[ "s" ∈ GStream Bool' ]
          constantly-if (g-headB ∙ var "s")
                        (g-consB ∙ mod-intro constantly true
                                 ∙ (next (g-consB ∙ mod-intro constantly false ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s"))))
                        (g-consB ∙ mod-intro constantly false
                                 ∙ (next (g-consB ∙ mod-intro constantly true  ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s"))))

g-thumorse-sem : Tm ′◇ (′GStream ′Bool')
g-thumorse-sem = ⟦ g-thumorse ⟧tm

-- Γ ⊢ g-fibonacci-word : GStream Bool'
g-fibonacci-word : TmExpr ω
g-fibonacci-word =
  let liftSB▻ = lift▻ (GStream Bool') (GStream Bool')
      liftLSB▻ = lift▻ (▻ (GStream Bool')) (▻ (GStream Bool'))
  in
  löb[ "fw" ∈▻ (GStream Bool') ]
    g-consB ∙ mod-intro constantly false
            ∙ (g-consB ∙ mod-intro constantly true
                       ⟨$-later⟩' (liftLSB▻ ∙ (liftSB▻ ∙ f)) ∙
                            (g-tailB ⟨$-later⟩' liftSB▻ ∙ f ∙ var "fw"))
  where
    f : TmExpr ω
    f =
      löb[ "g" ∈▻ (GStream Bool' ⇛ GStream Bool') ]
        lam[ "s" ∈ GStream Bool' ]
          constantly-if (g-headB ∙ var "s")
                        (g-consB ∙ mod-intro constantly false ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s"))
                        (g-consB ∙ mod-intro constantly false ∙ next (
                                 g-consB ∙ mod-intro constantly true ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s")))

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
    löb[ "g" ∈▻ (GStream A ⇛ GStream B ⇛ GStream C) ]
      lam[ "xs" ∈ GStream A ]
        lam[ "ys" ∈ GStream B ]
          var "f" ∙ (g-head A ∙ var "xs")
                  ∙ (g-head B ∙ var "ys")
                  ∙ (var "g" ⊛⟨ later ⟩ g-tail A ∙ var "xs" ⊛⟨ later ⟩ g-tail B ∙ var "ys")

g-mergef-sem : Tm ′◇ ((′⟨ ′constantly ∣ ′Nat' ⟩ ′⇛ ′⟨ ′constantly ∣ ′Bool' ⟩ ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Bool' ′⇛ ′GStream ′Nat')
g-mergef-sem = ⟦ g-mergef Nat' Bool' Nat' ⟧tm


--------------------------------------------------
-- Examples that are not taken from a paper

-- Γ ⊢ g-zipWith A B C : ⟨ constantly ∣ A ⇛ B ⇛ C ⟩ ⇛ GStream A ⇛ GStream B ⇛ GStream C
g-zipWith : (A B C : TyExpr ★) → TmExpr ω
g-zipWith A B C =
  lam[ "f" ∈ ⟨ constantly ∣ A ⇛ B ⇛ C ⟩ ]
    löb[ "g" ∈▻ (GStream A ⇛ GStream B ⇛ GStream C) ]
      lam[ "as" ∈ GStream A ]
        lam[ "bs" ∈ GStream B ]
          g-cons C ∙ (var "f" ⊛⟨ constantly ⟩ g-head A ∙ var "as" ⊛⟨ constantly ⟩ g-head B ∙ var "bs")
                   ∙ (var "g" ⊛⟨ later ⟩ g-tail A ∙ var "as" ⊛⟨ later ⟩ g-tail B ∙ var "bs")

g-zipWith-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Bool' ′⇛ ′Nat' ′⇛ ′Bool' ⟩ ′⇛ ′GStream ′Bool' ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Bool')
g-zipWith-sem = ⟦ g-zipWith Bool' Nat' Bool' ⟧tm

-- Γ ⊢ g-fibs : GStream Nat'
g-fibs : TmExpr ω
g-fibs =
  let lift2SN▻ = lift2▻ (GStream Nat') (GStream Nat') (GStream Nat')
  in
  löb[ "s" ∈▻ (GStream Nat') ]
    g-consN ∙ mod-intro constantly (lit 1)
            ∙ (g-consN ∙ mod-intro constantly (lit 1)
                       ⟨$-later⟩' (lift2SN▻ ∙ (g-zipWith Nat' Nat' Nat' ∙ mod-intro constantly plus)
                                            ∙ var "s"
                                            ⟨$-later⟩' (g-tailN ⟨$-later⟩' var "s")))

g-fibs-sem : Tm ′◇ (′GStream ′Nat')
g-fibs-sem = ⟦ g-fibs ⟧tm

-- Γ ⊢ g-flipFst A : GStream A ⇛ ▻ (GStream A)
g-flipFst : TyExpr ★ → TmExpr ω
g-flipFst A =
  lam[ "s" ∈ GStream A ]
    g-cons A ⟨$-later⟩' g-snd A ∙ var "s" ⊛⟨ later ⟩ next (
    g-cons A ⟨$-later⟩' next (g-head A ∙ var "s") ⊛⟨ later ⟩ (g-tail A ⟨$-later⟩' g-tail A ∙ var "s"))

g-flipFst-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′GStream ′Bool'))
g-flipFst-sem = ⟦ g-flipFst Bool' ⟧tm


--------------------------------------------------
--------------------------------------------------
-- Examples involving standard streams and the extraction
--   to Agda streams

Stream' : TyExpr ★ → TyExpr ★
Stream' A = ⟨ forever ∣ GStream A ⟩


--------------------------------------------------
-- Continuation of the example worked out in Sections 3, 5 and 6 of the CPP submission

-- Γ ⊢ nats : Stream' Nat'
nats : TmExpr ★
nats = mod-intro forever g-nats

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
paperfolds = mod-intro forever g-paperfolds

paperfolds-sem : Tm ′◇ (′Stream' ′Nat')
paperfolds-sem = ⟦ paperfolds ⟧tm

paperfolds-agda : Stream ℕ
paperfolds-agda = extract-term paperfolds-sem

paperfolds-test : take 10 paperfolds-agda ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
paperfolds-test = refl

-- Γ ⊢ thue-morse : Stream' Bool'
thue-morse : TmExpr ★
thue-morse = mod-intro forever g-thumorse

thue-morse-sem : Tm ′◇ (′Stream' ′Bool')
thue-morse-sem = ⟦ thue-morse ⟧tm

thue-morse-agda : Stream Bool
thue-morse-agda = extract-term thue-morse-sem

thue-morse-test : take 10 thue-morse-agda ≡ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ []
thue-morse-test = refl

-- Γ ⊢ fibonacci-word : Stream' Bool'
fibonacci-word : TmExpr ★
fibonacci-word = mod-intro forever g-fibonacci-word

fibonacci-word-sem : Tm ′◇ (′Stream' ′Bool')
fibonacci-word-sem = ⟦ fibonacci-word ⟧tm

fibonacci-word-agda : Stream Bool
fibonacci-word-agda = extract-term fibonacci-word-sem

fibonacci-word-test : take 10 fibonacci-word-agda ≡ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ []
fibonacci-word-test = refl

-- Γ ⊢ head' A : Stream' A ⇛ A
head' : TyExpr ★ → TmExpr ★
head' A = ann
  lam[ "s" ∈ Stream' A ] g-head A ⟨$- forever ⟩ var "s"
  ∈ (Stream' A ⇛ A)

head-nats : TmExpr ★
head-nats = head' Nat' ∙ nats

head-nats-agda : ℕ
head-nats-agda = extract-term (⟦ head-nats ⟧tm)

head-nats-test : head-nats-agda ≡ 0
head-nats-test = refl

-- Γ ⊢ tail' A : Stream' A ⇛ Stream' A
tail' : TyExpr ★ → TmExpr ★
tail' A = ann
  lam[ "s" ∈ Stream' A ] g-tail A ⟨$- forever ⟩ var "s"
  ∈ (Stream' A ⇛ Stream' A)

tailN-sem : Tm ′◇ (′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
tailN-sem = ⟦ tail' Nat' ⟧tm

-- Γ ⊢ cons' A : A ⇛ Stream' A ⇛ Stream' A
cons' : TyExpr ★ → TmExpr ★
cons' A = ann
  lam[ "a" ∈ A ] lam[ "as" ∈ Stream' A ]
    g-cons A ⟨$- forever ⟩ (ann (var "a") ∈ ⟨ forever ∣ ⟨ constantly ∣ A ⟩ ⟩)
             ⊛⟨ forever ⟩ (ann (var "as") ∈ ⟨ forever ∣ ⟨ later ∣ GStream A ⟩ ⟩)
  ∈ (A ⇛ Stream' A ⇛ Stream' A)

consB-sem : Tm ′◇ (′Bool' ′⇛ ′Stream' ′Bool' ′⇛ ′Stream' ′Bool')
consB-sem = ⟦ cons' Bool' ⟧tm

-- Γ ⊢ map' A B : (A ⇛ B) ⇛ Stream' A ⇛ Stream' B
map' : TyExpr ★ → TyExpr ★ → TmExpr ★
map' A B =
  lam[ "f" ∈ A ⇛ B ]
    lam[ "s" ∈ Stream' A ]
      g-map A B ⟨$- forever ⟩ ann (var "f") ∈ ⟨ forever ∣ ⟨ constantly ∣ A ⇛ B ⟩ ⟩
                ⊛⟨ forever ⟩ var "s"

map'-sem : Tm ′◇ ((′Nat' ′⇛ ′Nat') ′⇛ ′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
map'-sem = ⟦ map' Nat' Nat' ⟧tm

-- Γ ⊢ g-every2nd A : ⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A
g-every2nd : TyExpr ★ → TmExpr ω
g-every2nd A =
  löb[ "g" ∈▻ (⟨ constantly ∣ Stream' A ⟩ ⇛ GStream A) ]
    lam[ "s" ∈ ⟨ constantly ∣ Stream' A ⟩ ]
      g-cons A ∙ (head' A ⟨$- constantly ⟩ var "s")
               ∙ (var "g" ⊛⟨ later ⟩ next (tail' A ⟨$- constantly ⟩ (tail' A ⟨$- constantly ⟩ var "s")))

g-every2ndB-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Stream' ′Bool' ⟩ ′⇛ ′GStream ′Bool')
g-every2ndB-sem = ⟦ g-every2nd Bool' ⟧tm

-- Γ ⊢ every2nd A : Stream' A ⇛ Stream' A
every2nd : TyExpr ★ → TmExpr ★
every2nd A =
  lam[ "s" ∈ Stream' A ]
    g-every2nd A ⟨$- forever ⟩ ann (var "s") ∈ ⟨ forever ∣ ⟨ constantly ∣ Stream' A ⟩ ⟩

every2ndN-sem : Tm ′◇ (′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
every2ndN-sem = ⟦ every2nd Nat' ⟧tm

every2nd-test : take 6 (extract-term (every2ndN-sem $ nats-sem))
                ≡ 0 ∷ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ []
every2nd-test = refl

-- Γ ⊢ g-diag : ⟨ constantly ∣ Stream' (Stream' A) ⟩ ⇛ GStream A
g-diag : TyExpr ★ → TmExpr ω
g-diag A =
  löb[ "g" ∈▻ (⟨ constantly ∣ Stream' (Stream' A) ⟩ ⇛ GStream A) ]
    lam[ "xss" ∈ ⟨ constantly ∣ Stream' (Stream' A) ⟩ ]
      g-cons A ∙ (head' A ⟨$- constantly ⟩ (head' (Stream' A) ⟨$- constantly ⟩ var "xss"))
               ∙ (var "g" ⊛⟨ later ⟩ next (map' (Stream' A) (Stream' A) ∙ tail' A
                                                ⟨$- constantly ⟩ (tail' (Stream' A) ⟨$- constantly ⟩ var "xss")))

g-diagB-sem : Tm ′◇ (′⟨ ′constantly ∣ ′Stream' (′Stream' ′Bool') ⟩ ′⇛ ′GStream ′Bool')
g-diagB-sem = ⟦ g-diag Bool' ⟧tm

-- Γ ⊢ diag : Stream' (Stream' A) ⇛ Stream' A
diag : TyExpr ★ → TmExpr ★
diag A =
  lam[ "s" ∈ Stream' (Stream' A) ]
    g-diag A ⟨$- forever ⟩ ann (var "s") ∈ ⟨ forever ∣ ⟨ constantly ∣ Stream' (Stream' A) ⟩ ⟩

diagB-sem : Tm ′◇ (′Stream' (′Stream' ′Bool') ′⇛ ′Stream' ′Bool')
diagB-sem = ⟦ diag Bool' ⟧tm


--------------------------------------------------
-- Example not taken from a paper

-- Γ ⊢ fibs : Stream' Nat'
fibs : TmExpr ★
fibs = mod-intro forever g-fibs

fibs-sem : Tm ′◇ (′Stream' ′Nat')
fibs-sem = ⟦ fibs ⟧tm

fibs-agda : Stream ℕ
fibs-agda = extract-term fibs-sem

fibs-test : take 10 fibs-agda ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
fibs-test = refl
