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


e-consN = e-cons e-Nat
e-headN = e-head e-Nat
e-tailN = e-tail e-Nat

infixl 5 _⊛timeless_
_⊛timeless_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
f ⊛timeless t = e-mod-intro e-timeless (e-app (e-mod-elim e-timeless f) (e-mod-elim e-timeless t))

infixl 5 _e-⟨$⟩'_
_e-⟨$⟩'_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
f e-⟨$⟩' t = (e-next' f) e-⊛' t

-- e-lift▻' T takes a function of type T → S and produces a function of type ▻' T → ▻' S
e-lift▻' : TyExpr e-ω → TmExpr e-ω → TmExpr e-ω
e-lift▻' T f = e-lam (e-▻' T) (f e-⟨$⟩' e-var 0)

-- e-lift2▻' T S takes a function of type T → S → R and produces a function of type ▻' T → ▻' S → ▻' R
e-lift2▻' : TyExpr e-ω → TyExpr e-ω → TmExpr e-ω → TmExpr e-ω
e-lift2▻' T S f = e-lam (e-▻' T) (e-lam (e-▻' S) (f e-⟨$⟩' e-var 1 e-⊛' e-var 0))

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
    e-löb (e-GStream e-Nat e→ e-GStream e-Nat) (
      e-lam (e-GStream e-Nat) (
        e-app (e-app e-consN
                     (e-var 2 ⊛timeless e-app e-headN (e-var 0)))
              (e-var 1 e-⊛' e-app e-tailN (e-var 0)))))

⟦g-map⟧sikkel : Tm ◇ (timeless-ty (Nat' ⇛ Nat') ⇛ GStream Nat' ⇛ GStream Nat')
⟦g-map⟧sikkel = ⟦ g-map ⟧tm-in e-◇

{-
g-nats : Tm Γ (GStream Nat')
g-nats = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero'
                                             $ (g-map $ timeless-tm suc') ⟨$⟩' varι "s"
-}

g-nats : TmExpr e-ω
g-nats =
  e-löb (e-GStream e-Nat) (
    e-app (e-app e-consN
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
g-snd = e-lam (e-GStream e-Nat) (e-headN e-⟨$⟩' e-app e-tailN (e-var 0))

g-thrd : TmExpr e-ω
g-thrd = e-lam (e-GStream e-Nat) (g-snd e-⟨$⟩' e-app e-tailN (e-var 0))

g-zeros : TmExpr e-ω
g-zeros = e-löb (e-GStream e-Nat) (e-app (e-app e-consN (e-mod-intro e-timeless (e-lit 0))) (e-var 0))

⟦g-snd⟧sikkel : Tm ◇ (GStream Nat' ⇛ ▻' (timeless-ty Nat'))
⟦g-snd⟧sikkel = ⟦ g-snd ⟧tm-in e-◇

⟦g-thrd⟧sikkel : Tm ◇ (GStream Nat' ⇛ ▻' (▻' (timeless-ty Nat')))
⟦g-thrd⟧sikkel = ⟦ g-thrd ⟧tm-in e-◇

⟦g-zeros⟧sikkel : Tm ◇ (GStream Nat')
⟦g-zeros⟧sikkel = ⟦ g-zeros ⟧tm-in e-◇

{-
g-iterate' : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
            Tm Γ (timeless-ty (A ⇛ A) ⇛ timeless-ty A ⇛ GStream A)
g-iterate' {A = A} =
  lamι[ "f" ∈ timeless-ty (A ⇛ A) ]
    löbι[ "g" ∈▻' (timeless-ty A ⇛ GStream A) ]
      lamι[ "x" ∈ timeless-ty A ]
        g-cons $ varι "x"
               $ varι "g" ⊛' next' (varι "f" ⊛⟨ timeless ⟩ varι "x")
-}

g-iterate' : TmExpr e-ω
g-iterate' =
  e-lam (e-mod e-timeless (e-Nat e→ e-Nat)) (
    e-löb ((e-mod e-timeless e-Nat) e→ e-GStream e-Nat) (
      e-lam (e-mod e-timeless e-Nat) (
        e-app (e-app e-consN
                     (e-var 0))
              ((e-var 1) e-⊛' (e-next' (e-var 2 ⊛timeless e-var 0))))))

⟦g-iterate'⟧sikkel : Tm ◇ (timeless-ty (Nat' ⇛ Nat') ⇛ timeless-ty Nat' ⇛ GStream Nat')
⟦g-iterate'⟧sikkel = ⟦ g-iterate' ⟧tm-in e-◇

{-
g-iterate : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
             Tm Γ (▻' (timeless-ty (A ⇛ A)) ⇛ timeless-ty A ⇛ GStream A)
g-iterate {A = A} =
  lamι[ "f" ∈ ▻' (timeless-ty (A ⇛ A)) ]
    lamι[ "a" ∈ timeless-ty A ]
      löbι[ "s" ∈▻' GStream A ]
        g-cons $ varι "a"
               $ g-map ⟨$⟩' varι "f" ⊛' varι "s"
-}

g-iterate : TmExpr e-ω
g-iterate =
  e-lam (e-▻' (e-mod e-timeless (e-Nat e→ e-Nat))) (
    e-lam (e-mod e-timeless e-Nat) (
      e-löb (e-GStream e-Nat) (
        e-app (e-app e-consN
                     (e-var 1))
              (g-map e-⟨$⟩' e-var 2 e-⊛' e-var 0))))

⟦g-iterate⟧sikkel : Tm ◇ (▻' (timeless-ty (Nat' ⇛ Nat')) ⇛ timeless-ty Nat' ⇛ GStream Nat')
⟦g-iterate⟧sikkel = ⟦ g-iterate ⟧tm-in e-◇

{-
g-nats' : Tm Γ (GStream Nat')
g-nats' = g-iterate $ next' (timeless-tm suc') $ timeless-tm zero'
-}

g-nats' : TmExpr e-ω
g-nats' = e-app (e-app g-iterate (e-next' (e-mod-intro e-timeless e-suc))) (e-mod-intro e-timeless (e-lit 0))

⟦g-nats'⟧sikkel : Tm ◇ (GStream Nat')
⟦g-nats'⟧sikkel = ⟦ g-nats' ⟧tm-in e-◇

{-
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
-}

g-interleave : TmExpr e-ω
g-interleave =
  e-löb (e-GStream e-Nat e→ (e-▻' (e-GStream e-Nat)) e→ e-GStream e-Nat) (
    e-lam (e-GStream e-Nat) (
      e-lam (e-▻' (e-GStream e-Nat)) (
        e-app (e-app e-consN
                     (e-app e-headN (e-var 1)))
              (e-var 2 e-⊛' e-var 0 e-⊛' e-next' (e-app e-tailN (e-var 1))))))

g-toggle : TmExpr e-ω
g-toggle = e-löb (e-GStream e-Nat) (e-app (e-app e-consN
                                          (e-mod-intro e-timeless (e-lit 1)))
                                   (e-next' (e-app (e-app e-consN
                                                          (e-mod-intro e-timeless (e-lit 0)))
                                                   (e-var 0))))

g-paperfolds : TmExpr e-ω
g-paperfolds = e-löb (e-GStream e-Nat) (e-app (e-app g-interleave g-toggle) (e-var 0))

⟦g-interleave⟧sikkel : Tm ◇ (GStream Nat' ⇛ ▻' (GStream Nat') ⇛ GStream Nat')
⟦g-interleave⟧sikkel = ⟦ g-interleave ⟧tm-in e-◇

⟦g-toggle⟧sikkel : Tm ◇ (GStream Nat')
⟦g-toggle⟧sikkel = ⟦ g-toggle ⟧tm-in e-◇

⟦g-paperfolds⟧sikkel : Tm ◇ (GStream Nat')
⟦g-paperfolds⟧sikkel = ⟦ g-paperfolds ⟧tm-in e-◇

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
  e-löb ((((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat)) e→ e-Nat) e→ e-GStream e-Nat e→ e-Nat) (
    e-lam ((((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat)) e→ e-Nat)) (
      e-lam (e-GStream e-Nat) (
        e-app (e-var 1) (e-pair (e-app e-headN (e-var 0))
                                (e-var 2 e-⊛' e-next' (e-var 1) e-⊛' e-app e-tailN (e-var 0))))))

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
  e-löb ((e-Nat e→ ((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat))) e→ e-Nat e→ e-GStream e-Nat) (
    e-lam (e-Nat e→ ((e-mod e-timeless e-Nat) e-⊠ (e-▻' e-Nat))) (
      e-lam e-Nat (
        e-app (e-app e-consN
                     (e-fst (e-app (e-var 1) (e-var 0))))
              (e-var 2 e-⊛' e-next' (e-var 1) e-⊛' e-snd (e-app (e-var 1) (e-var 0))))))

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
  e-lam ((e-mod e-timeless e-Nat) e→ (e-mod e-timeless e-Nat) e→ (e-▻' (e-GStream e-Nat)) e→ e-GStream e-Nat) (
    e-löb (e-GStream e-Nat e→ e-GStream e-Nat e→ e-GStream e-Nat) (
      e-lam (e-GStream e-Nat) (
        e-lam (e-GStream e-Nat) (
          e-app (e-app (e-app (e-var 3)
                              (e-app e-headN (e-var 1)))
                       (e-app e-headN (e-var 0)))
                (e-var 2 e-⊛' e-app e-tailN (e-var 1) e-⊛' e-app e-tailN (e-var 0))))))

⟦g-mergef⟧sikkel : Tm ◇ ((timeless-ty Nat' ⇛ timeless-ty Nat' ⇛ ▻' (GStream Nat') ⇛ GStream Nat') ⇛ GStream Nat' ⇛ GStream Nat' ⇛ GStream Nat')
⟦g-mergef⟧sikkel = ⟦ g-mergef ⟧tm-in e-◇

{-
g-zipWith : {A B C : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} → {{IsClosedNatural C}} →
            Tm Γ (timeless-ty (A ⇛ B ⇛ C)) → Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
g-zipWith {A = A}{B}{C} f =
  löbι[ "g" ∈▻' (GStream A ⇛ GStream B ⇛ GStream C) ]
    lamι[ "as" ∈ GStream A ]
      lamι[ "bs" ∈ GStream B ]
        g-cons $ ↑ι⟨ 3 ⟩ f ⊛⟨ timeless ⟩ (g-head $ varι "as") ⊛⟨ timeless ⟩ (g-head $ varι "bs")
               $ varι "g" ⊛' (g-tail $ varι "as") ⊛' (g-tail $ varι "bs")
-}

g-zipWith : TmExpr e-ω
g-zipWith =
  e-lam (e-mod e-timeless (e-Nat e→ e-Nat e→ e-Nat)) (
    e-löb (e-GStream e-Nat e→ e-GStream e-Nat e→ e-GStream e-Nat) (
      e-lam (e-GStream e-Nat) (
        e-lam (e-GStream e-Nat) (
          e-app (e-app e-consN
                       (e-var 3 ⊛timeless e-app e-headN (e-var 1) ⊛timeless e-app e-headN (e-var 0)))
                (e-var 2 e-⊛' e-app e-tailN (e-var 1) e-⊛' e-app e-tailN (e-var 0))))))

⟦g-zipWith⟧sikkel : Tm ◇ (timeless-ty (Nat' ⇛ Nat' ⇛ Nat') ⇛ GStream Nat' ⇛ GStream Nat' ⇛ GStream Nat')
⟦g-zipWith⟧sikkel = ⟦ g-zipWith ⟧tm-in e-◇

{-
g-fibs : Tm Γ (GStream Nat')
g-fibs = löbι[ "s" ∈▻' GStream Nat' ]
  g-cons $ timeless-tm one' $ (
  (g-cons $ timeless-tm one') ⟨$⟩'
  ((lift2▻' (g-zipWith (timeless-tm nat-sum)) $ varι "s") ⟨$⟩' (g-tail ⟨$⟩' varι "s")))
-}

g-fibs : TmExpr e-ω
g-fibs =
  e-löb (e-GStream e-Nat) (
    e-app (e-app e-consN
                 (e-mod-intro e-timeless (e-lit 1)))
          (e-app e-consN (e-mod-intro e-timeless (e-lit 1))
            e-⟨$⟩'
              (e-app (e-lift2▻' (e-GStream e-Nat) (e-GStream e-Nat) (e-app g-zipWith (e-mod-intro e-timeless e-plus))) (e-var 0)
                e-⟨$⟩'
                  (e-tailN e-⟨$⟩' e-var 0))))

⟦g-fibs⟧sikkel : Tm ◇ (GStream Nat')
⟦g-fibs⟧sikkel = ⟦ g-fibs ⟧tm-in e-◇



e-Stream : TyExpr e-★
e-Stream = e-mod e-allnow (e-GStream e-Nat)

e-nats : TmExpr e-★
e-nats = e-mod-intro e-allnow g-nats

⟦e-nats⟧sikkel : Tm ◇ (Stream' Nat')
⟦e-nats⟧sikkel = ⟦ e-nats ⟧tm-in e-◇

⟦e-nats⟧agda : Stream ℕ
⟦e-nats⟧agda = translate-term ⟦e-nats⟧sikkel

e-nats-test : take 10 ⟦e-nats⟧agda ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
e-nats-test = refl

e-paperfolds : TmExpr e-★
e-paperfolds = e-mod-intro e-allnow g-paperfolds

⟦e-paperfolds⟧sikkel : Tm ◇ (Stream' Nat')
⟦e-paperfolds⟧sikkel = ⟦ e-paperfolds ⟧tm-in e-◇

⟦e-paperfolds⟧agda : Stream ℕ
⟦e-paperfolds⟧agda = translate-term ⟦e-paperfolds⟧sikkel

e-paperfolds-test : take 10 ⟦e-paperfolds⟧agda ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
e-paperfolds-test = refl

e-fibs : TmExpr e-★
e-fibs = e-mod-intro e-allnow g-fibs

⟦e-fibs⟧sikkel : Tm ◇ (Stream' Nat')
⟦e-fibs⟧sikkel = ⟦ e-fibs ⟧tm-in e-◇

⟦e-fibs⟧agda : Stream ℕ
⟦e-fibs⟧agda = translate-term ⟦e-fibs⟧sikkel

e-fibs-test : take 10 ⟦e-fibs⟧agda ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
e-fibs-test = refl
