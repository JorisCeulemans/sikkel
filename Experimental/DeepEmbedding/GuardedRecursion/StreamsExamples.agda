module Experimental.DeepEmbedding.GuardedRecursion.StreamsExamples where

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (take; head; tail)
open import Relation.Binary.PropositionalEquality

open import CwF-Structure hiding (_,,_; var) renaming (◇ to ′◇)
open import Types.Discrete renaming (Nat' to ′Nat'; Bool' to ′Bool')
open import Types.Functions hiding (lam; app) renaming (_⇛_ to _′⇛_)
open import Types.Products hiding (pair; fst; snd) renaming (_⊠_ to _′⊠_)
open import Types.Instances
open import GuardedRecursion.Modalities hiding (timeless; allnow; later; next; löb; lift▻; lift2▻; 𝟙≤later) renaming (▻ to ′▻)
open import GuardedRecursion.Streams.Guarded hiding (g-cons; g-head; g-tail) renaming (GStream to ′GStream)
open import GuardedRecursion.Streams.Standard hiding (cons'; head'; tail') renaming (Stream' to ′Stream')
open import Translation

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker


g-consN = g-cons Nat'
g-headN = g-head Nat'
g-tailN = g-tail Nat'

infixl 5 _⊛⟨_⟩_
_⊛⟨_⟩_ : ∀ {m m'} → TmExpr m → ModalityExpr m' m → TmExpr m → TmExpr m
f ⊛⟨ μ ⟩ t = mod-intro μ (mod-elim μ f ∙ mod-elim μ t)

infixl 5 _⟨$-_⟩_
_⟨$-_⟩_ : ∀ {m m'} → TmExpr m' → ModalityExpr m' m → TmExpr m → TmExpr m
f ⟨$- μ ⟩ t = mod-intro μ (f ∙ mod-elim μ t)

next : TmExpr ω → TmExpr ω
next t = coe[ 𝟙≤later ∈ 𝟙 ⇒ later ] mod-intro 𝟙 t

-- lift▻ T takes a function of type T → S and produces a function of type ▻ T → ▻ S
lift▻ : TyExpr ω → TmExpr ω → TmExpr ω
lift▻ T f = lam (▻ T) (f ⟨$- later ⟩ var 0)

-- lift2▻ T S takes a function of type T → S → R and produces a function of type ▻ T → ▻ S → ▻ R
lift2▻ : TyExpr ω → TyExpr ω → TmExpr ω → TmExpr ω
lift2▻ T S f = lam (▻ T) (lam ( ▻ S) (f ⟨$- later ⟩ var 1 ⊛⟨ later ⟩ var 0))

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

g-map : TmExpr ω
g-map =
  lam ⟨ timeless ∣ Nat' ⇛ Nat' ⟩ (
    löb (GStream Nat' ⇛ GStream Nat') (
      lam (GStream Nat') (
        g-consN ∙ (var 2 ⊛⟨ timeless ⟩ g-headN ∙ var 0)
                ∙ (var 1 ⊛⟨ later ⟩ g-tailN ∙ var 0))))

⟦g-map⟧sikkel : Tm ′◇ (timeless-ty (′Nat' ′⇛ ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat')
⟦g-map⟧sikkel = ⟦ g-map ⟧tm-in ◇

{-
g-nats : Tm Γ (GStream Nat')
g-nats = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero'
                                             $ (g-map $ timeless-tm suc') ⟨$⟩' varι "s"
-}

g-nats : TmExpr ω
g-nats =
  löb (GStream Nat') (
    g-consN ∙ mod-intro timeless (lit 0)
            ∙ ((g-map ∙ mod-intro timeless suc) ⟨$- later ⟩ var 0))

⟦g-nats⟧sikkel : Tm ′◇ (′GStream ′Nat')
⟦g-nats⟧sikkel = ⟦ g-nats ⟧tm-in ◇

{-
g-snd : Tm Γ (GStream A ⇛ ▻' (timeless-ty A))
g-snd = lamι[ "s" ∈ GStream A ] g-head ⟨$⟩' (g-tail $ varι "s")

g-thrd : Tm Γ (GStream A ⇛ ▻' (▻' (timeless-ty A)))
g-thrd = lamι[ "s" ∈ GStream A ] g-snd ⟨$⟩' (g-tail $ varι "s")

g-zeros : Tm Γ (GStream Nat')
g-zeros = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero' $ varι "s"
-}

g-snd : TmExpr ω
g-snd = lam (GStream Nat') (g-headN ⟨$- later ⟩ g-tailN ∙ var 0)

g-thrd : TmExpr ω
g-thrd = lam (GStream Nat') (g-snd ⟨$- later ⟩ g-tailN ∙ var 0)

g-zeros : TmExpr ω
g-zeros = löb (GStream Nat') (g-consN ∙ mod-intro timeless (lit 0) ∙ var 0)

⟦g-snd⟧sikkel : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (timeless-ty ′Nat'))
⟦g-snd⟧sikkel = ⟦ g-snd ⟧tm-in ◇

⟦g-thrd⟧sikkel : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (′▻ (timeless-ty ′Nat')))
⟦g-thrd⟧sikkel = ⟦ g-thrd ⟧tm-in ◇

⟦g-zeros⟧sikkel : Tm ′◇ (′GStream ′Nat')
⟦g-zeros⟧sikkel = ⟦ g-zeros ⟧tm-in ◇

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

g-iterate' : TmExpr ω
g-iterate' =
  lam ⟨ timeless ∣ Nat' ⇛ Nat' ⟩ (
    löb (⟨ timeless ∣ Nat' ⟩ ⇛ GStream Nat') (
      lam ⟨ timeless ∣ Nat' ⟩ (
        g-consN ∙ var 0
                ∙ (var 1 ⊛⟨ later ⟩ (next (var 2 ⊛⟨ timeless ⟩ var 0))))))

⟦g-iterate'⟧sikkel : Tm ′◇ (timeless-ty (′Nat' ′⇛ ′Nat') ′⇛ timeless-ty ′Nat' ′⇛ ′GStream ′Nat')
⟦g-iterate'⟧sikkel = ⟦ g-iterate' ⟧tm-in ◇

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

g-iterate : TmExpr ω
g-iterate =
  lam (▻ ⟨ timeless ∣ Nat' ⇛ Nat' ⟩) (
    lam ⟨ timeless ∣ Nat' ⟩ (
      löb (GStream Nat') (
        g-consN ∙ var 1
                ∙ (g-map ⟨$- later ⟩ var 2 ⊛⟨ later ⟩ var 0))))

⟦g-iterate⟧sikkel : Tm ′◇ (′▻ (timeless-ty (′Nat' ′⇛ ′Nat')) ′⇛ timeless-ty ′Nat' ′⇛ ′GStream ′Nat')
⟦g-iterate⟧sikkel = ⟦ g-iterate ⟧tm-in ◇

{-
g-nats' : Tm Γ (GStream Nat')
g-nats' = g-iterate $ next' (timeless-tm suc') $ timeless-tm zero'
-}

g-nats' : TmExpr ω
g-nats' = g-iterate ∙ next (mod-intro timeless suc) ∙ mod-intro timeless (lit 0)

⟦g-nats'⟧sikkel : Tm ′◇ (′GStream ′Nat')
⟦g-nats'⟧sikkel = ⟦ g-nats' ⟧tm-in ◇

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

g-interleave : TmExpr ω
g-interleave =
  löb (GStream Nat' ⇛ ▻ (GStream Nat') ⇛ GStream Nat') (
    lam (GStream Nat') (
      lam (▻ (GStream Nat')) (
        g-consN ∙ (g-headN ∙ var 1)
                ∙ (var 2 ⊛⟨ later ⟩ var 0 ⊛⟨ later ⟩ next (g-tailN ∙ var 1)))))

g-toggle : TmExpr ω
g-toggle = löb (GStream Nat') (g-consN ∙ (mod-intro timeless (lit 1))
                                       ∙ (next (g-consN ∙ mod-intro timeless (lit 0) ∙ var 0)))

g-paperfolds : TmExpr ω
g-paperfolds = löb (GStream Nat') (g-interleave ∙ g-toggle ∙ var 0)

⟦g-interleave⟧sikkel : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat')
⟦g-interleave⟧sikkel = ⟦ g-interleave ⟧tm-in ◇

⟦g-toggle⟧sikkel : Tm ′◇ (′GStream ′Nat')
⟦g-toggle⟧sikkel = ⟦ g-toggle ⟧tm-in ◇

⟦g-paperfolds⟧sikkel : Tm ′◇ (′GStream ′Nat')
⟦g-paperfolds⟧sikkel = ⟦ g-paperfolds ⟧tm-in ◇

{-
g-initial : Tm Γ (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T)
g-initial =
  löbι[ "g" ∈▻' (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T) ]
    lamι[ "f" ∈ (timeless-ty A ⊠ ▻' T) ⇛ T ]
      lamι[ "s" ∈ GStream A ]
        varι "f" $ pair (g-head $ varι "s")
                        (varι "g" ⊛' next' (varι "f") ⊛' (g-tail $ varι "s"))
-}

g-initial : TmExpr ω
g-initial =
  löb (((⟨ timeless ∣ Nat' ⟩ ⊠ (▻ Bool')) ⇛ Bool') ⇛ GStream Nat' ⇛ Bool') (
    lam (((⟨ timeless ∣ Nat' ⟩ ⊠ (▻ Bool')) ⇛ Bool')) (
      lam (GStream Nat') (
        var 1 ∙ (pair (g-headN ∙ (var 0))
                      (var 2 ⊛⟨ later ⟩ next (var 1) ⊛⟨ later ⟩ g-tailN ∙ var 0)))))

⟦g-initial⟧sikkel : Tm ′◇ (((timeless-ty ′Nat' ′⊠ ′▻ ′Bool') ′⇛ ′Bool') ′⇛ ′GStream ′Nat' ′⇛ ′Bool')
⟦g-initial⟧sikkel = ⟦ g-initial ⟧tm-in ◇

{-
g-final : Tm Γ ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A)
g-final =
  löbι[ "g" ∈▻' ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A) ]
    lamι[ "f" ∈ T ⇛ (timeless-ty A ⊠ ▻' T) ]
      lamι[ "x" ∈ T ]
        g-cons $ fst (varι "f" $ varι "x")
               $ varι "g" ⊛' next' (varι "f") ⊛' snd (varι "f" $ varι "x")
-}

g-final : TmExpr ω
g-final =
  löb ((Bool' ⇛ (⟨ timeless ∣ Nat' ⟩ ⊠ (▻ Bool'))) ⇛ Bool' ⇛ GStream Nat') (
    lam (Bool' ⇛ (⟨ timeless ∣ Nat' ⟩ ⊠ (▻ Bool'))) (
      lam Bool' (
        g-consN ∙ (fst (var 1 ∙ var 0))
                ∙ (var 2 ⊛⟨ later ⟩ next (var 1) ⊛⟨ later ⟩ snd (var 1 ∙ var 0)))))

⟦g-final⟧sikkel : Tm ′◇ ((′Bool' ′⇛ (timeless-ty ′Nat' ′⊠ ′▻ ′Bool')) ′⇛ ′Bool' ′⇛ ′GStream ′Nat')
⟦g-final⟧sikkel = ⟦ g-final ⟧tm-in ◇

{-
thumorse : Tm Γ (GStream Bool')
thumorse = löbι[ "t-m" ∈▻' GStream Bool' ]
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
-}

g-consB = g-cons Bool'
g-headB = g-head Bool'
g-tailB = g-tail Bool'

g-thumorse : TmExpr ω
g-thumorse =
  let liftSB▻ = lift▻ (GStream Bool')
      liftLSB▻ = lift▻ (▻ (GStream Bool'))
  in
  löb (GStream Bool') (
    g-consB ∙ mod-intro timeless false
            ∙ (g-consB ∙ (mod-intro timeless true)
                       ⟨$- later ⟩ (liftLSB▻ (liftSB▻ h)) ∙
                            (g-tailB ⟨$- later ⟩ liftSB▻ h ∙ var 0)))
  where
    h : TmExpr ω
    h =
      löb (GStream Bool' ⇛ GStream Bool') (
        lam (GStream Bool') (
          timeless-if (g-headB ∙ var 0)
                      (g-consB ∙ mod-intro timeless true
                               ∙ (next (g-consB ∙ mod-intro timeless false ∙ (var 1 ⊛⟨ later ⟩ g-tailB ∙ var 0))))
                      (g-consB ∙ mod-intro timeless false
                               ∙ (next (g-consB ∙ mod-intro timeless true  ∙ (var 1 ⊛⟨ later ⟩ g-tailB ∙ var 0))))))

⟦g-thumorse⟧sikkel : Tm ′◇ (′GStream ′Bool')
⟦g-thumorse⟧sikkel = ⟦ g-thumorse ⟧tm-in ◇

{-
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
            else' (g-cons $ timeless-tm false' $ next' (g-cons $ timeless-tm true' $ varι "g" ⊛' (g-tail $ varι "s"))))
-}

g-fibonacci-word : TmExpr ω
g-fibonacci-word =
  let liftSB▻ = lift▻ (GStream Bool')
      liftLSB▻ = lift▻ (▻ (GStream Bool'))
  in
  löb (GStream Bool') (
    g-consB ∙ mod-intro timeless false
            ∙ (g-consB ∙ mod-intro timeless true
                       ⟨$- later ⟩ (liftLSB▻ (liftSB▻ f)) ∙
                            (g-tailB ⟨$- later ⟩ liftSB▻ f ∙ var 0)))
  where
    f : TmExpr ω
    f =
      löb (GStream Bool' ⇛ GStream Bool') (
        lam (GStream Bool') (
          timeless-if (g-headB ∙ var 0)
                      (g-consB ∙ mod-intro timeless false ∙ (var 1 ⊛⟨ later ⟩ g-tailB ∙ var 0))
                      (g-consB ∙ mod-intro timeless false ∙ next (
                          g-consB ∙ mod-intro timeless true ∙ (var 1 ⊛⟨ later ⟩ g-tailB ∙ var 0)))))

⟦g-fibonacci-word⟧sikkel : Tm ′◇ (′GStream ′Bool')
⟦g-fibonacci-word⟧sikkel = ⟦ g-fibonacci-word ⟧tm-in ◇

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

g-mergef : TmExpr ω
g-mergef =
  lam (⟨ timeless ∣ Nat' ⟩ ⇛ ⟨ timeless ∣ Nat' ⟩ ⇛ (▻ (GStream Nat')) ⇛ GStream Nat') (
    löb (GStream Nat' ⇛ GStream Nat' ⇛ GStream Nat') (
      lam (GStream Nat') (
        lam (GStream Nat') (
          var 3 ∙ (g-headN ∙ var 1)
                ∙ (g-headN ∙ var 0)
                ∙ (var 2 ⊛⟨ later ⟩ g-tailN ∙ var 1 ⊛⟨ later ⟩ g-tailN ∙ var 0)))))

⟦g-mergef⟧sikkel : Tm ′◇ ((timeless-ty ′Nat' ′⇛ timeless-ty ′Nat' ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat')
⟦g-mergef⟧sikkel = ⟦ g-mergef ⟧tm-in ◇

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

g-zipWith : TmExpr ω
g-zipWith =
  lam ⟨ timeless ∣ Nat' ⇛ Nat' ⇛ Nat' ⟩ (
    löb (GStream Nat' ⇛ GStream Nat' ⇛ GStream Nat') (
      lam (GStream Nat') (
        lam (GStream Nat') (
          g-consN ∙ (var 3 ⊛⟨ timeless ⟩ g-headN ∙ var 1 ⊛⟨ timeless ⟩ g-headN ∙ var 0)
                  ∙ (var 2 ⊛⟨ later ⟩ g-tailN ∙ var 1 ⊛⟨ later ⟩ g-tailN ∙ var 0)))))

⟦g-zipWith⟧sikkel : Tm ′◇ (timeless-ty (′Nat' ′⇛ ′Nat' ′⇛ ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat')
⟦g-zipWith⟧sikkel = ⟦ g-zipWith ⟧tm-in ◇

{-
g-fibs : Tm Γ (GStream Nat')
g-fibs = löbι[ "s" ∈▻' GStream Nat' ]
  g-cons $ timeless-tm one' $ (
  (g-cons $ timeless-tm one') ⟨$⟩'
  ((lift2▻' (g-zipWith (timeless-tm nat-sum)) $ varι "s") ⟨$⟩' (g-tail ⟨$⟩' varι "s")))
-}

g-fibs : TmExpr ω
g-fibs =
  let lift2SN▻ = lift2▻ (GStream Nat') (GStream Nat')
      lift2LSN▻ = lift2▻ (▻ (GStream Nat')) (▻ (GStream Nat'))
  in
  löb (GStream Nat') (
    g-consN ∙ mod-intro timeless (lit 1)
            ∙ (g-consN ∙ mod-intro timeless (lit 1)
                       ⟨$- later ⟩ (lift2LSN▻ (lift2SN▻ (g-zipWith ∙ mod-intro timeless plus))
                                              ∙ next (var 0)
                                              ∙ (g-tailN ⟨$- later ⟩ var 0))))

⟦g-fibs⟧sikkel : Tm ′◇ (′GStream ′Nat')
⟦g-fibs⟧sikkel = ⟦ g-fibs ⟧tm-in ◇

{-
g-flipFst : {A : ClosedType ★} → {{IsClosedNatural A}} →
            Tm Γ (GStream A ⇛ ▻' (GStream A))
g-flipFst {A = A}= lamι[ "s" ∈ GStream A ]
                     g-cons ⟨$⟩' (g-snd $ varι "s") ⊛' next' (
                     g-cons ⟨$⟩' next' (g-head $ varι "s") ⊛' (g-tail ⟨$⟩' (g-tail $ varι "s")))
-}

g-flipFst : TmExpr ω
g-flipFst =
  lam (GStream Nat') (
    g-consN ⟨$- later ⟩ g-snd ∙ var 0 ⊛⟨ later ⟩ next (
    g-consN ⟨$- later ⟩ next (g-headN ∙ var 0) ⊛⟨ later ⟩ (g-tailN ⟨$- later ⟩ g-tailN ∙ var 0)))

⟦g-flipFst⟧sikkel : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (′GStream ′Nat'))
⟦g-flipFst⟧sikkel = ⟦ g-flipFst ⟧tm-in ◇



Stream' : TyExpr ★ → TyExpr ★
Stream' A = ⟨ allnow ∣ GStream A ⟩

nats : TmExpr ★
nats = mod-intro allnow g-nats

⟦nats⟧sikkel : Tm ′◇ (′Stream' ′Nat')
⟦nats⟧sikkel = ⟦ nats ⟧tm-in ◇

⟦nats⟧agda : Stream ℕ
⟦nats⟧agda = translate-term ⟦nats⟧sikkel

nats-test : take 10 ⟦nats⟧agda ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
nats-test = refl

paperfolds : TmExpr ★
paperfolds = mod-intro allnow g-paperfolds

⟦paperfolds⟧sikkel : Tm ′◇ (′Stream' ′Nat')
⟦paperfolds⟧sikkel = ⟦ paperfolds ⟧tm-in ◇

⟦paperfolds⟧agda : Stream ℕ
⟦paperfolds⟧agda = translate-term ⟦paperfolds⟧sikkel

paperfolds-test : take 10 ⟦paperfolds⟧agda ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
paperfolds-test = refl

thue-morse : TmExpr ★
thue-morse = mod-intro allnow g-thumorse

⟦thue-morse⟧sikkel : Tm ′◇ (′Stream' ′Bool')
⟦thue-morse⟧sikkel = ⟦ thue-morse ⟧tm-in ◇

⟦thue-morse⟧agda : Stream Bool
⟦thue-morse⟧agda = translate-term ⟦thue-morse⟧sikkel

thue-morse-test : take 10 ⟦thue-morse⟧agda ≡ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ []
thue-morse-test = refl

fibonacci-word : TmExpr ★
fibonacci-word = mod-intro allnow g-fibonacci-word

⟦fibonacci-word⟧sikkel : Tm ′◇ (′Stream' ′Bool')
⟦fibonacci-word⟧sikkel = ⟦ fibonacci-word ⟧tm-in ◇

⟦fibonacci-word⟧agda : Stream Bool
⟦fibonacci-word⟧agda = translate-term ⟦fibonacci-word⟧sikkel

fibonacci-word-test : take 10 ⟦fibonacci-word⟧agda ≡ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ []
fibonacci-word-test = refl

fibs : TmExpr ★
fibs = mod-intro allnow g-fibs

⟦fibs⟧sikkel : Tm ′◇ (′Stream' ′Nat')
⟦fibs⟧sikkel = ⟦ fibs ⟧tm-in ◇

⟦fibs⟧agda : Stream ℕ
⟦fibs⟧agda = translate-term ⟦fibs⟧sikkel

fibs-test : take 10 ⟦fibs⟧agda ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
fibs-test = refl


head : TyExpr ★ → TmExpr ★
head A = ann
  lam (Stream' A) (g-head A ⟨$- allnow ⟩ var 0)
  ∈ (Stream' A ⇛ A)

head-nats : TmExpr ★
head-nats = head Nat' ∙ nats

⟦head-nats⟧agda : ℕ
⟦head-nats⟧agda = translate-term (⟦ head-nats ⟧tm-in ◇)

head-nats-test : ⟦head-nats⟧agda ≡ 0
head-nats-test = refl

tail : TyExpr ★ → TmExpr ★
tail A = ann
  lam (Stream' A) (g-tail A ⟨$- allnow ⟩ var 0)
  ∈ (Stream' A ⇛ Stream' A)

cons : TyExpr ★ → TmExpr ★
cons A = ann
  lam A (lam (Stream' A) (g-cons A
                           ⟨$- allnow ⟩ (ann var 1 ∈ ⟨ allnow ∣ ⟨ timeless ∣ A ⟩ ⟩)
                           ⊛⟨ allnow ⟩ (ann var 0 ∈ ⟨ allnow ∣ ⟨ later ∣ GStream A ⟩ ⟩)))
  ∈ (A ⇛ Stream' A ⇛ Stream' A)
