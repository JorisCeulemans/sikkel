--------------------------------------------------
-- Examples of programming with guarded streams in Sikkel
--------------------------------------------------

module GuardedRecursion.Streams.Examples.Guarded where

open import Data.Bool using (if_then_else_; true; false)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Instances
open import Modalities
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded
open import Reflection.Naturality.TypeOperations
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.LobInduction

private
  variable
    Γ Δ : Ctx ω


--------------------------------------------------
-- Example from the introduction and section 3.1 of the ICFP submission

g-map : {A B : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} →
        Tm Γ (timeless-ty (A ⇛ B) ⇛ GStream A ⇛ GStream B)
g-map {A = A}{B} =
  lamι[ "f" ∈ timeless-ty (A ⇛ B) ]
    löbι[ "m" ∈▻' (GStream A ⇛ GStream B) ]
      lamι[ "s" ∈ GStream A ]
        g-cons $ varι "f" ⊛⟨ timeless ⟩ (g-head $ varι "s")
               $ varι "m" ⊛' (g-tail $ varι "s")

g-nats : Tm Γ (GStream Nat')
g-nats = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero'
                                             $ (g-map $ timeless-tm suc') ⟨$⟩' varι "s"


--------------------------------------------------
-- The follwing definitions are an implementation of all examples involving streams on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The Guarded Lambda-Calculus: Programming and Reasoning with Guarded Recursion for Coinductive Types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.
--   https://doi.org/10.2168/LMCS-12(3:7)2016

module _ {A : ClosedType ★} {{_ : IsClosedNatural A}} where
  
  g-snd : Tm Γ (GStream A ⇛ ▻' (timeless-ty A))
  g-snd = lamι[ "s" ∈ GStream A ] g-head ⟨$⟩' (g-tail $ varι "s")

  g-thrd : Tm Γ (GStream A ⇛ ▻' (▻' (timeless-ty A)))
  g-thrd = lamι[ "s" ∈ GStream A ] g-snd ⟨$⟩' (g-tail $ varι "s")

g-zeros : Tm Γ (GStream Nat')
g-zeros = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero' $ varι "s"

private
  module _ {Γ : Ctx ω} where
    zeros-test : g-head {Γ = Γ} $ g-zeros ≅ᵗᵐ timeless-tm zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : g-snd {Γ = Γ} $ g-zeros ≅ᵗᵐ next' (timeless-tm zero')
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

g-iterate' : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
            Tm Γ (timeless-ty (A ⇛ A) ⇛ timeless-ty A ⇛ GStream A)
g-iterate' {A = A} =
  lamι[ "f" ∈ timeless-ty (A ⇛ A) ]
    löbι[ "g" ∈▻' (timeless-ty A ⇛ GStream A) ]
      lamι[ "x" ∈ timeless-ty A ]
        g-cons $ varι "x"
               $ varι "g" ⊛' next' (varι "f" ⊛⟨ timeless ⟩ varι "x")

-- This is a more general definition of iterate since the generating function of type
-- timeless-ty (A ⇛ A) appears under ▻'. The implementation itself applies g-map to
-- its corecursive call (represented by the variable "s"), which would not be allowed
-- in a definition of standard Agda streams by copattern matching.
g-iterate : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
             Tm Γ (▻' (timeless-ty (A ⇛ A)) ⇛ timeless-ty A ⇛ GStream A)
g-iterate {A = A} =
  lamι[ "f" ∈ ▻' (timeless-ty (A ⇛ A)) ]
    lamι[ "a" ∈ timeless-ty A ]
      löbι[ "s" ∈▻' GStream A ]
        g-cons $ varι "a"
               $ g-map ⟨$⟩' varι "f" ⊛' varι "s"

-- Alternative definition of g-nats making use of g-iterate.
g-nats' : Tm Γ (GStream Nat')
g-nats' = g-iterate $ next' (timeless-tm suc') $ timeless-tm zero'

g-interleave : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
               Tm Γ (GStream A ⇛ ▻' (GStream A) ⇛ GStream A)
g-interleave {A = A} =
  löbι[ "g" ∈▻' (GStream A ⇛ ▻' (GStream A) ⇛ GStream A) ]
    lamι[ "s" ∈ GStream A ]
      lamι[ "t" ∈ ▻' (GStream A) ]
        g-cons $ (g-head $ varι "s")
               $ varι "g" ⊛' varι "t" ⊛' next' (g-tail $ varι "s")

g-toggle : Tm Γ (GStream Nat')
g-toggle = löbι[ "s" ∈▻' GStream Nat' ]
             g-cons $ timeless-tm one'
                    $ next' (g-cons $ timeless-tm zero' $ varι "s")

g-paperfolds : Tm Γ (GStream Nat')
g-paperfolds = löbι[ "s" ∈▻' GStream Nat' ] g-interleave $ g-toggle $ varι "s"

module _
  (A : ClosedType ★) {{_ : IsClosedNatural A}}
  (T : ClosedType ω) {{_ : IsClosedNatural T}}
  where
  g-initial : Tm Γ (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T)
  g-initial =
    löbι[ "g" ∈▻' (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T) ]
      lamι[ "f" ∈ (timeless-ty A ⊠ ▻' T) ⇛ T ]
        lamι[ "s" ∈ GStream A ]
          varι "f" $ (pair $ (g-head $ varι "s")
                           $ (varι "g" ⊛' next' (varι "f") ⊛' (g-tail $ varι "s")))

  g-final : Tm Γ ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A)
  g-final =
    löbι[ "g" ∈▻' ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A) ]
      lamι[ "f" ∈ T ⇛ (timeless-ty A ⊠ ▻' T) ]
        lamι[ "x" ∈ T ]
          g-cons $ (fst $ (varι "f" $ varι "x"))
                 $ varι "g" ⊛' next' (varι "f") ⊛' (snd $ (varι "f" $ varι "x"))


--------------------------------------------------
-- Implementation of the examples on page 12 of the paper by Clouston et al. cited above.

thue-morse : Tm Γ (GStream Bool')
thue-morse = löbι[ "t-m" ∈▻' GStream Bool' ]
  g-cons $ timeless-tm false' $ (
  g-cons $ timeless-tm true') ⟨$⟩' (
  lift▻' (lift▻' h) $ (g-tail ⟨$⟩' (lift▻' h $ varι "t-m")))
  where
    h : Tm Δ (GStream Bool' ⇛ GStream Bool')
    h = löbι[ "g" ∈▻' GStream Bool' ⇛ GStream Bool' ]
          lamι[ "s" ∈ GStream Bool' ] (
            timeless-if' (g-head $ varι "s")
            then' (g-cons $ timeless-tm true'  $ next' (g-cons $ timeless-tm false' $ varι "g" ⊛' (g-tail $ varι "s")))
            else' (g-cons $ timeless-tm false' $ next' (g-cons $ timeless-tm true'  $ varι "g" ⊛' (g-tail $ varι "s"))))

fibonacci-word : Tm Γ (GStream Bool')
fibonacci-word = löbι[ "fw" ∈▻' GStream Bool' ]
  g-cons $ timeless-tm false' $ (
  g-cons $ timeless-tm true') ⟨$⟩' (
  lift▻' (lift▻' f) $ (g-tail ⟨$⟩' (lift▻' f $ varι "fw")))
  where
    f : Tm Δ (GStream Bool' ⇛ GStream Bool')
    f = löbι[ "g" ∈▻' GStream Bool' ⇛ GStream Bool' ]
          lamι[ "s" ∈ GStream Bool' ] (
            timeless-if' (g-head $ varι "s")
            then' (g-cons $ timeless-tm false' $ varι "g" ⊛' (g-tail $ varι "s"))
            else' (g-cons $ timeless-tm false' $ next' (g-cons $ timeless-tm true'  $ varι "g" ⊛' (g-tail $ varι "s"))))


--------------------------------------------------
-- This is an implementation of an example from the end of section 1.1 of the paper
--   Robert Atkey, and Conor McBride.
--   Productive Coprogramming with Guarded Recursion.
--   ICFP 2013.
--   https://doi.org/10.1145/2544174.2500597

g-mergef : {A B C : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} → {{IsClosedNatural C}} →
           Tm Γ (timeless-ty A ⇛ timeless-ty B ⇛ ▻' (GStream C) ⇛ GStream C) →
           Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
g-mergef {A = A}{B}{C} f =
  löbι[ "g" ∈▻' (GStream A ⇛ GStream B ⇛ GStream C) ]
    lamι[ "xs" ∈ GStream A ]
      lamι[ "ys" ∈ GStream B ]
        (↑ι⟨ 3 ⟩ f) $ (g-head $ varι "xs")
                    $ (g-head $ varι "ys")
                    $ (varι "g" ⊛' (g-tail $ varι "xs") ⊛' (g-tail $ varι "ys"))


--------------------------------------------------
-- Examples that are not taken from a paper

g-zipWith : {A B C : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} → {{IsClosedNatural C}} →
            Tm Γ (timeless-ty (A ⇛ B ⇛ C)) → Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
g-zipWith {A = A}{B}{C} f =
  löbι[ "g" ∈▻' (GStream A ⇛ GStream B ⇛ GStream C) ]
    lamι[ "as" ∈ GStream A ]
      lamι[ "bs" ∈ GStream B ]
        g-cons $ ↑ι⟨ 3 ⟩ f ⊛⟨ timeless ⟩ (g-head $ varι "as") ⊛⟨ timeless ⟩ (g-head $ varι "bs")
               $ varι "g" ⊛' (g-tail $ varι "as") ⊛' (g-tail $ varι "bs")

-- The stream of fibonacci numbers.
g-fibs : Tm Γ (GStream Nat')
g-fibs = löbι[ "s" ∈▻' GStream Nat' ]
  g-cons $ timeless-tm one' $ (
  (g-cons $ timeless-tm one') ⟨$⟩'
  ((lift2▻' (g-zipWith (timeless-tm nat-sum)) $ varι "s") ⟨$⟩' (g-tail ⟨$⟩' varι "s")))

-- g-flipFst flips the first two elements of a guarded stream.
g-flipFst : {A : ClosedType ★} → {{IsClosedNatural A}} →
            Tm Γ (GStream A ⇛ ▻' (GStream A))
g-flipFst {A = A}= lamι[ "s" ∈ GStream A ]
                     g-cons ⟨$⟩' (g-snd $ varι "s") ⊛' next' (
                     g-cons ⟨$⟩' next' (g-head $ varι "s") ⊛' (g-tail ⟨$⟩' (g-tail $ varι "s")))
