--------------------------------------------------
-- Examples with standard streams in mode ★
--------------------------------------------------

module GuardedRecursion.Streams.Standard where

open import Data.Nat
open import Data.Unit
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import Types.Products
open import Types.Instances
open import GuardedRecursion.Streams.Guarded
open import GuardedRecursion.Modalities
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.Naturality
open import Reflection.SubstitutionSequence

private
  variable
    Γ : Ctx ★


--------------------------------------------------
-- Definition of Stream' & corresponding constructor and destructors

Stream' : ClosedType ★ → ClosedType ★
Stream' A = allnow-ty (GStream A)

instance
  stream'-natural : {A : ClosedType ★} {{_ : IsClosedNatural A}} → IsClosedNatural (Stream' A)
  closed-natural {{stream'-natural}} σ =
    ≅ᵗʸ-trans (allnow-ty-natural σ) (allnow-ty-cong
              (≅ᵗʸ-trans (gstream-natural (timeless-subst σ)) (gstream-cong
                         (closed-natural (now-subst (timeless-subst σ))))))

module _ {A : ClosedType ★} {{_ : IsClosedNatural A}} where
  allnow-timeless-ty-nul : {Γ : Ctx ★} → allnow-ty (timeless-ty A) ≅ᵗʸ A {Γ = Γ}
  allnow-timeless-ty-nul = ≅ᵗʸ-trans by-naturality allnow-timeless-ty

  head' : Tm Γ (Stream' A ⇛ A)
  head' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ allnow-timeless-ty-nul ] allnow-tm (g-head $ unallnow-tm (varι "s"))

  tail' : Tm Γ (Stream' A ⇛ Stream' A)
  tail' = lamι[ "s" ∈ Stream' A ] ι[ allnow-later'-ty ] allnow-tm (g-tail $ unallnow-tm (varι "s"))

  cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
  cons' = lamι[ "x" ∈ A ]
            lamι[ "xs" ∈ Stream' A ]
              allnow-tm (g-cons $ unallnow-tm (ι[ allnow-timeless-ty-nul ] varι "x")
                                $ unallnow-tm (ι⁻¹[ allnow-later'-ty ] varι "xs"))


--------------------------------------------------
-- Examples of standard streams & functions on standard streams, implemented in Sikkel

-- The example from the introduction and section 3.1 of the ICFP submission
nats' : Tm Γ (Stream' Nat')
nats' = allnow-tm g-nats

paperfolds' : Tm Γ (Stream' Nat')
paperfolds' = allnow-tm g-paperfolds

fibs' : Tm Γ (Stream' Nat')
fibs' = allnow-tm g-fibs

now-timeless-ctx-intro : {A : ClosedType ★} {{_ : IsClosedNatural A}} {Γ : Ctx ★} →
                         Tm Γ A → Tm (now (timeless-ctx Γ)) A
now-timeless-ctx-intro t = ι[ by-naturality ] (t [ from now-timeless-ctx ]')

instance
  ⇛-closed : {A B : ClosedType ★} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
             IsClosedNatural (A ⇛ B)
  closed-natural {{⇛-closed}} σ = by-naturality


-- The following are implementations of all examples involving streams on page 11 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The Guarded Lambda-Calculus: Programming and Reasoning with Guarded Recursion for Coinductive Types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.
--   https://doi.org/10.2168/LMCS-12(3:7)2016

map' : {A B : ClosedType ★} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
       Tm Γ ((A ⇛ B) ⇛ Stream' A ⇛ Stream' B)
map' {A = A}{B = B} =
  lamι[ "f" ∈ A ⇛ B ]
    lamι[ "s" ∈ Stream' A ]
      allnow-tm (g-map $ timeless-tm (now-timeless-ctx-intro (varι "f"))
                       $ unallnow-tm (varι "s"))

open import Reflection.Tactic.LobInduction

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
