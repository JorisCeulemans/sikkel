{-# OPTIONS --allow-unsolved-metas --omega-in-omega #-}

module Translation where

open import Function using (_∘_)
open import Data.Product using (_×_) renaming (_,_ to [_,_])
open import Data.Sum using (_⊎_; map) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Sum.Relation.Binary.Pointwise renaming (inj₁ to inl; inj₂ to inr)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import Helpers
open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums
open import GuardedRecursion.Streams.Standard
open import Reflection.Naturality
open import Reflection.Naturality.Instances


record Translatable (T : NullaryTypeOp ★) : Set₁ where
  field
    translated-type : Set
    translate-term  : Tm ◇ T → translated-type
    translate-back  : translated-type → Tm ◇ T
    translate-cong  : {t s : Tm ◇ T} → t ≅ᵗᵐ s → translate-term t ≡ translate-term s

open Translatable {{...}} public

translate-type : (T : NullaryTypeOp ★) → {{Translatable T}} → Set
translate-type T = translated-type {T = T}

instance
  translate-discr : {A : Set} → Translatable (Discr A)
  translated-type {{translate-discr {A = A}}} = A
  translate-term  {{translate-discr {A = A}}} t = t ⟨ tt , tt ⟩'
  translate-back  {{translate-discr {A = A}}} a = discr a
  translate-cong  {{translate-discr {A = A}}} e = eq e tt

  translate-prod : {T : NullaryTypeOp ★}  {{_ : Translatable T}}
                   {S : NullaryTypeOp ★} {{_ : Translatable S}} →
                   Translatable (T ⊠ S)
  translated-type {{translate-prod {T = T} {S = S}}} = translate-type T × translate-type S
  translate-term  {{translate-prod {T = T} {S = S}}} p = [ translate-term (fst p) , translate-term (snd p) ]
  translate-back  {{translate-prod {T = T} {S = S}}} [ t , s ] = pair (translate-back t) (translate-back s)
  translate-cong  {{translate-prod {T = T} {S = S}}} e = cong₂ [_,_] (translate-cong (fst-cong e)) (translate-cong (snd-cong e))

expose-sum-term : {A : Ty {C = ★} ◇} {B : Ty ◇} →
                  Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
expose-sum-term {A = A}{B = B} p with p ⟨ tt , tt ⟩'
... | inl a = inl (MkTm (λ { tt tt → a }) (λ { tt refl → morph-id A a }))
... | inr b = inr (MkTm (λ { tt tt → b }) (λ { tt refl → morph-id B b }))

expose-sum-cong : {A : Ty {C = ★} ◇} {B : Ty ◇} {t s : Tm ◇ (A ⊞ B)} →
                  t ≅ᵗᵐ s → Pointwise _≅ᵗᵐ_ _≅ᵗᵐ_ (expose-sum-term t) (expose-sum-term s)
expose-sum-cong {t = t}{s = s} e with t ⟨ tt , tt ⟩' | s ⟨ tt , tt ⟩' | eq e tt
... | inl a | .(inl a) | refl = inl (record { eq = λ _ → refl })
... | inr b | .(inr b) | refl = inr (record { eq = λ _ → refl })

instance
  translate-sum : {T : NullaryTypeOp ★}  {{_ : Translatable T}}
                  {S : NullaryTypeOp ★} {{_ : Translatable S}} →
                  Translatable (T ⊞ S)
  translated-type {{translate-sum {T = T} {S = S}}} = translate-type T ⊎ translate-type S
  translate-term  {{translate-sum {T = T} {S = S}}} p = map translate-term translate-term (expose-sum-term p)
  translate-back  {{translate-sum {T = T} {S = S}}} (inl t) = inl' (translate-back t)
  translate-back  {{translate-sum {T = T} {S = S}}} (inr s) = inr' (translate-back s)
  translate-cong  {{translate-sum {T = T} {S = S}}} {t = p}{s = q} e with expose-sum-term p | expose-sum-term q | expose-sum-cong e
  ... | inl t1 | inl t2 | inl et = cong inl (translate-cong et)
  ... | inr s1 | inr s2 | inr es = cong inr (translate-cong es)

to-★-◇-term : {T : Ty {C = ★} ◇} → T ⟨ tt , tt ⟩ → Tm ◇ T
term (to-★-◇-term t) _ _ = t
Tm.naturality (to-★-◇-term {T = T} t) _ refl = morph-id T t

func-★-◇ : {T : Ty {C = ★} ◇} {S : Ty {C = ★} ◇} →
           (Tm ◇ T → Tm ◇ S) → Tm ◇ (T ⇛ S)
_$⟨_,_⟩_ (term (func-★-◇ {T = T} f) _ _) _ refl t = f (to-★-◇-term t) ⟨ tt , tt ⟩'
PresheafFunc.naturality (term (func-★-◇ {T = T}{S = S} f) _ _) {ρ-xy = _} refl refl t =
  trans (cong (λ x → term (f (to-★-◇-term x)) tt tt) (morph-id T t)) (sym (morph-id S _))
Tm.naturality (func-★-◇ f) _ refl = to-pshfun-eq (λ { _ refl _ → refl })

instance
  translate-func : {T : NullaryTypeOp ★}  {{_ : Translatable T}}
                   {S : NullaryTypeOp ★} {{_ : Translatable S}} →
                   Translatable (T ⇛ S)
  translated-type {{translate-func {T = T} {S = S}}} = translate-type T → translate-type S
  translate-term  {{translate-func {T = T} {S = S}}} f t = translate-term (app f (translate-back t))
  translate-back  {{translate-func {T = T} {S = S}}} f = func-★-◇ (translate-back ∘ f ∘ translate-term)
  translate-cong  {{translate-func {T = T} {S = S}}} ef = funext λ x → translate-cong (app-cong ef ≅ᵗᵐ-refl)


open import Reflection.Naturality
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.Lambda
open import Reflection.Naturality.Instances

nat-sum : Tm {C = ★} ◇ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = nat-elim (Nat' ⇛ Nat')
                   (lamι[ "n" ∈ Nat' ] varι "n")
                   (lamι[ "f" ∈ Nat' ⇛ Nat' ]
                     lamι[ "n" ∈ Nat' ] suc' $ (varι "f" $ varι "n"))

nat-sum-β : (m n : Tm {C = ★} ◇ Nat') → app (app nat-sum (suc' $ m)) n ≅ᵗᵐ suc' $ (app (app nat-sum m) n)
nat-sum-β m n = {!!}

open import Data.Nat

_+'_ : ℕ → ℕ → ℕ
_+'_ = translate-term nat-sum

test : 6 +' 3 ≡ 9
test = refl

test2 : (n : ℕ) → 0 +' n ≡ n
test2 n = refl

test3 : (n : ℕ) → 1 +' n ≡ suc n
test3 n = refl

test4 : (n : ℕ) → 2 +' n ≡ suc (suc n)
test4 n = refl

test5 : (n : ℕ) → n +' 0 ≡ n
test5 zero    = refl
test5 (suc n) = {!cong suc (test5 n)!}

test6 : (m n : ℕ) → suc m +' n ≡ suc (m +' n)
test6 m n = {!translate-cong {T = Nat'}
                           {t = app (app nat-sum (suc' (discr m))) (discr n)}
                           {s = suc' (app (app nat-sum (discr m)) (discr n))}
                           {!nat-sum-β (discr m) (discr n)!}!}


open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Properties
open import GuardedRecursion.Streams.Guarded using (first-≤; map-first-≤; first-≤-refl; g-paperfolds; g-fibs)

record Stream (A : Set ℓ) : Set ℓ where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

take : {A : Set ℓ} (n : ℕ) → Stream A → Vec A n
take zero    s = []
take (suc n) s = head s ∷ take n (tail s)

take-first : {A : Set ℓ} {m n : ℕ} (m≤n : m ≤ n) (s : Stream A) →
             first-≤ m≤n (take n s) ≡ take m s
take-first z≤n       s = refl
take-first (s≤s m≤n) s = cong (head s ∷_) (take-first m≤n (tail s))


open import GuardedRecursion.Modalities
instance
  translate-stream : {A : NullaryTypeOp ★} {{_ : IsNullaryNatural A}} {{_ : Translatable A}} → Translatable (Stream' A)
  translated-type {{translate-stream {A = A}}} = Stream (translate-type A)
  head (translate-term {{translate-stream}} s) = translate-term (head' $ s)
  tail (translate-term {{translate-stream}} s) = translate-term (tail' $ s)
  translate-back {{translate-stream {A = A}}} s = allnow-tm (MkTm (λ n _ → Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩')
                                                                                        (take (suc n) s))
                                                                  (λ { m≤n refl → nat (s≤s m≤n) s }))
    where
      open ≡-Reasoning
      nat : ∀ {m n} (m≤n : m ≤ n) (s' : Stream (translate-type A)) →
        Data.Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩') (take n s')))
          ≡ Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩') (take m s')
      nat {m}{n} m≤n s' = begin
          Data.Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩') (take n s')))
        ≡⟨ trans (map-cong (morph-id A) _) (map-id _) ⟩
          first-≤ m≤n (Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩') (take n s'))
        ≡˘⟨ map-first-≤ _ m≤n (take n s') ⟩
          Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩') (first-≤ m≤n (take n s'))
        ≡⟨ cong (Data.Vec.map _) (take-first m≤n s') ⟩
          Data.Vec.map (λ a → now-timeless-ctx-nul {A = A} (translate-back a) ⟨ tt , tt ⟩') (take m s') ∎
  translate-cong {{translate-stream}} = {!!} -- not provable unless you assume that bisimilarity implies equality of streams

paperfolds : Stream ℕ
paperfolds = translate-term paperfolds'

fibs : Stream ℕ
fibs = translate-term fibs'

private
  fibs-test : take 10 fibs ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷
                             8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
  fibs-test = refl

  paperfolds-test : take 10 paperfolds ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
  paperfolds-test = refl
