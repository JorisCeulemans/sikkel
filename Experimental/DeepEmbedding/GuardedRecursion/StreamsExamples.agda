module Experimental.DeepEmbedding.GuardedRecursion.StreamsExamples where

open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (take)
open import Relation.Binary.PropositionalEquality

open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import Types.Products
open import Types.Instances
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded
open import GuardedRecursion.Streams.Standard
open import Translation

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker


_⊛timeless_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
f ⊛timeless t = e-mod-intro e-timeless (e-app (e-mod-elim e-timeless f) (e-mod-elim e-timeless t))

_e-⟨$⟩'_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
f e-⟨$⟩' t = e-⊛' (e-next' f) t

{-
g-map : {A B : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} →
        Tm Γ (timeless-ty (A ⇛ B) ⇛ GStream A ⇛ GStream B)
g-map {A = A}{B} =
  lamι[ "f" ∈ timeless-ty (A ⇛ B) ]
    löbι[ "m" ∈▻' (GStream A ⇛ GStream B) ]
      lamι[ "s" ∈ GStream A ]
        g-cons $ varι "f" ⊛⟨ timeless ⟩ (g-head $ varι "s")
               $ varι "m" ⊛' (g-tail $ varι "s")
-}

g-map : TmExpr e-ω
g-map =
  e-lam (e-mod e-timeless (e-Nat e→ e-Nat)) (
    e-löb (e-GStreamN e→ e-GStreamN) (
      e-lam e-GStreamN (
        e-app (e-app e-cons
                     (e-var 2 ⊛timeless e-app e-head (e-var 0)))
              (e-⊛' (e-var 1) (e-app e-tail (e-var 0))))))

⟦g-map⟧sikkel : Tm ◇ (timeless-ty (Nat' ⇛ Nat') ⇛ GStream Nat' ⇛ GStream Nat')
⟦g-map⟧sikkel = ⟦ g-map ⟧tm-in e-◇

{-
g-nats : Tm Γ (GStream Nat')
g-nats = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero'
                                             $ (g-map $ timeless-tm suc') ⟨$⟩' varι "s"
-}

g-nats : TmExpr e-ω
g-nats =
  e-löb e-GStreamN (
    e-app (e-app e-cons
                 (e-mod-intro e-timeless (e-lit 0)))
          (e-app g-map (e-mod-intro e-timeless e-suc) e-⟨$⟩' e-var 0))

⟦g-nats⟧sikkel : Tm ◇ (GStream Nat')
⟦g-nats⟧sikkel = ⟦ g-nats ⟧tm-in e-◇

{-
g-snd : Tm Γ (GStream A ⇛ ▻' (timeless-ty A))
g-snd = lamι[ "s" ∈ GStream A ] g-head ⟨$⟩' (g-tail $ varι "s")

g-thrd : Tm Γ (GStream A ⇛ ▻' (▻' (timeless-ty A)))
g-thrd = lamι[ "s" ∈ GStream A ] g-snd ⟨$⟩' (g-tail $ varι "s")

g-zeros : Tm Γ (GStream Nat')
g-zeros = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero' $ varι "s"
-}

g-snd : TmExpr e-ω
g-snd = e-lam e-GStreamN (e-head e-⟨$⟩' e-app e-tail (e-var 0))

g-thrd : TmExpr e-ω
g-thrd = e-lam e-GStreamN (g-snd e-⟨$⟩' e-app e-tail (e-var 0))

g-zeros : TmExpr e-ω
g-zeros = e-löb e-GStreamN (e-app (e-app e-cons (e-mod-intro e-timeless (e-lit 0))) (e-var 0))

⟦g-snd⟧sikkel : Tm ◇ (GStream Nat' ⇛ ▻' (timeless-ty Nat'))
⟦g-snd⟧sikkel = ⟦ g-snd ⟧tm-in e-◇

⟦g-thrd⟧sikkel : Tm ◇ (GStream Nat' ⇛ ▻' (▻' (timeless-ty Nat')))
⟦g-thrd⟧sikkel = ⟦ g-thrd ⟧tm-in e-◇

⟦g-zeros⟧sikkel : Tm ◇ (GStream Nat')
⟦g-zeros⟧sikkel = ⟦ g-zeros ⟧tm-in e-◇

{-
g-initial : Tm Γ (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T)
g-initial =
  löbι[ "g" ∈▻' (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T) ]
    lamι[ "f" ∈ (timeless-ty A ⊠ ▻' T) ⇛ T ]
      lamι[ "s" ∈ GStream A ]
        varι "f" $ pair (g-head $ varι "s")
                        (varι "g" ⊛' next' (varι "f") ⊛' (g-tail $ varι "s"))
-}

g-initial : TmExpr e-ω
g-initial =
  e-löb ((((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat)) e→ e-Nat) e→ e-GStreamN e→ e-Nat) (
    e-lam ((((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat)) e→ e-Nat)) (
      e-lam e-GStreamN (
        e-app (e-var 1) (e-pair (e-app e-head (e-var 0))
                                (e-⊛' (e-⊛' (e-var 2) (e-next' (e-var 1))) (e-app e-tail (e-var 0)))))))

⟦g-initial⟧sikkel : Tm ◇ (((timeless-ty Nat' ⊠ ▻' Nat') ⇛ Nat') ⇛ GStream Nat' ⇛ Nat')
⟦g-initial⟧sikkel = ⟦ g-initial ⟧tm-in e-◇

{-
g-final : Tm Γ ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A)
g-final =
  löbι[ "g" ∈▻' ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A) ]
    lamι[ "f" ∈ T ⇛ (timeless-ty A ⊠ ▻' T) ]
      lamι[ "x" ∈ T ]
        g-cons $ fst (varι "f" $ varι "x")
               $ varι "g" ⊛' next' (varι "f") ⊛' snd (varι "f" $ varι "x")
-}

g-final : TmExpr e-ω
g-final =
  e-löb ((e-Nat e→ ((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat))) e→ e-Nat e→ e-GStreamN) (
    e-lam (e-Nat e→ ((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat))) (
      e-lam e-Nat (
        e-app (e-app e-cons
                     (e-fst (e-app (e-var 1) (e-var 0))))
              (e-⊛' (e-⊛' (e-var 2) (e-next' (e-var 1))) (e-snd (e-app (e-var 1) (e-var 0)))))))

⟦g-final⟧sikkel : Tm ◇ ((Nat' ⇛ (timeless-ty Nat' ⊠ ▻' Nat')) ⇛ Nat' ⇛ GStream Nat')
⟦g-final⟧sikkel = ⟦ g-final ⟧tm-in e-◇

{-
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
-}

g-mergef : TmExpr e-ω
g-mergef =
  e-lam ((e-mod e-timeless e-Nat) e→ (e-mod e-timeless e-Nat) e→ (e-▻' e-GStreamN) e→ e-GStreamN) (
    e-löb (e-GStreamN e→ e-GStreamN e→ e-GStreamN) (
      e-lam e-GStreamN (
        e-lam e-GStreamN (
          e-app (e-app (e-app (e-var 3)
                              (e-app e-head (e-var 1)))
                       (e-app e-head (e-var 0)))
                (e-⊛' (e-⊛' (e-var 2) (e-app e-tail (e-var 1))) (e-app e-tail (e-var 0)))))))

⟦g-mergef⟧sikkel : Tm ◇ ((timeless-ty Nat' ⇛ timeless-ty Nat' ⇛ ▻' (GStream Nat') ⇛ GStream Nat') ⇛ GStream Nat' ⇛ GStream Nat' ⇛ GStream Nat')
⟦g-mergef⟧sikkel = ⟦ g-mergef ⟧tm-in e-◇


e-Stream : TyExpr e-★
e-Stream = e-mod e-allnow e-GStreamN

e-nats : TmExpr e-★
e-nats = e-mod-intro e-allnow g-nats

⟦e-nats⟧sikkel : Tm ◇ (Stream' Nat')
⟦e-nats⟧sikkel = ⟦ e-nats ⟧tm-in e-◇

⟦e-nats⟧agda : Stream ℕ
⟦e-nats⟧agda = translate-term ⟦e-nats⟧sikkel

e-nats-test : take 10 ⟦e-nats⟧agda ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
e-nats-test = refl
