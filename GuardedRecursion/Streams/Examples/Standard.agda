--------------------------------------------------
-- Examples of standard streams & functions on standard streams, implemented in Sikkel
--------------------------------------------------

module GuardedRecursion.Streams.Examples.Standard where

open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Instances
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded
open import GuardedRecursion.Streams.Standard
open import GuardedRecursion.Streams.Examples.Guarded
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.Naturality
open import Reflection.Tactic.LobInduction
open import Translation

private
  variable
    Γ : Ctx ★


--------------------------------------------------
-- The example from the introduction and section 3.1 of the ICFP submission

nats' : Tm Γ (Stream' Nat')
nats' = allnow-tm g-nats

nats : Stream ℕ
nats = translate-term nats'

private
  nats-test : take 10 nats ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  nats-test = refl


--------------------------------------------------
-- The following are implementations of all examples involving streams on page 11 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The Guarded Lambda-Calculus: Programming and Reasoning with Guarded Recursion for Coinductive Types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.
--   https://doi.org/10.2168/LMCS-12(3:7)2016

paperfolds' : Tm Γ (Stream' Nat')
paperfolds' = allnow-tm g-paperfolds

map' : {A B : ClosedType ★} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
       Tm Γ ((A ⇛ B) ⇛ Stream' A ⇛ Stream' B)
map' {Γ = Γ}{A = A}{B = B} =
  lamι[ "f" ∈ A ⇛ B ]
    lamι[ "s" ∈ Stream' A ]
      allnow-tm (g-map $ timeless-tm (now-timeless-ctx-intro (varι "f"))
                       $ unallnow-tm (varι "s"))


module _ {A : ClosedType ★} {{_ : IsClosedNatural A}} {Γ : Ctx ω} where
  g-every2nd : Tm Γ (timeless-ty (Stream' A) ⇛ GStream A)
  g-every2nd = löbι[ "g" ∈▻' (timeless-ty (Stream' A) ⇛ GStream A) ]
                 lamι[ "s" ∈ timeless-ty (Stream' A) ]
                   g-cons $ timeless-tm (head' $ untimeless-tm (varι "s"))
                          $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "s"))))

  g-diag : Tm Γ (timeless-ty (Stream' (Stream' A)) ⇛ GStream A)
  g-diag = löbι[ "g" ∈▻' (timeless-ty (Stream' (Stream' A)) ⇛ GStream A) ]
             lamι[ "xss" ∈ timeless-ty (Stream' (Stream' A)) ]
               g-cons $ timeless-tm (head' $ (head' $ untimeless-tm (varι "xss")))
                      $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "xss"))))

every2nd : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
           Tm Γ (Stream' A ⇛ Stream' A)
every2nd {A = A} = lamι[ "s" ∈ Stream' A ] allnow-tm (
                     g-every2nd $ timeless-tm (now-timeless-ctx-intro (varι "s")))

diag : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
       Tm Γ (Stream' (Stream' A) ⇛ Stream' A)
diag {A = A} = lamι[ "xss" ∈ Stream' (Stream' A) ] allnow-tm (
                 g-diag $ timeless-tm (now-timeless-ctx-intro (varι "xss")))


--------------------------------------------------
-- Other examples not taken from a paper

paperfolds : Stream ℕ
paperfolds = translate-term paperfolds'

fibs' : Tm Γ (Stream' Nat')
fibs' = allnow-tm g-fibs

fibs : Stream ℕ
fibs = translate-term fibs'

private

  fibs-test : take 10 fibs ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
  fibs-test = refl

  paperfolds-test : take 10 paperfolds ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
  paperfolds-test = refl
