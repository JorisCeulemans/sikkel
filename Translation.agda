module Translation where

open import Data.Product using (_×_; _,_)
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
open import GuardedRecursion.Modalities renaming (Stream to Stream'; head to head'; tail to tail')

private
  variable
    ℓc : Level


record Translatable (T : Ty {C = ★} ◇ ℓ) : Set (lsuc ℓ) where
  field
    translated-type : Set ℓ
    translate-term  : Tm ◇ T → translated-type
    translate-back  : translated-type → Tm ◇ T
    translate-cong  : {t s : Tm ◇ T} → t ≅ᵗᵐ s → translate-term t ≡ translate-term s

open Translatable {{...}} public

translate-type : (T : Ty {C = ★} ◇ ℓ) → {{Translatable T}} → Set ℓ
translate-type T = translated-type {T = T}

expose-sum-term : {A : Ty {C = ★} ◇ ℓ} {B : Ty ◇ ℓ'} →
                  Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
expose-sum-term {A = A}{B = B} p with p ⟨ tt , tt ⟩'
... | inl a = inl (MkTm (λ { tt tt → a }) (λ { tt refl → morph-id A a }))
... | inr b = inr (MkTm (λ { tt tt → b }) (λ { tt refl → morph-id B b }))

expose-sum-cong : {A : Ty {C = ★} ◇ ℓ} {B : Ty ◇ ℓ'} {t s : Tm ◇ (A ⊞ B)} →
                  t ≅ᵗᵐ s → Pointwise _≅ᵗᵐ_ _≅ᵗᵐ_ (expose-sum-term t) (expose-sum-term s)
expose-sum-cong {t = t}{s = s} e with t ⟨ tt , tt ⟩' | s ⟨ tt , tt ⟩' | eq e tt
... | inl a | .(inl a) | refl = inl (record { eq = λ _ → refl })
... | inr b | .(inr b) | refl = inr (record { eq = λ _ → refl })

instance
  translate-discr : {A : Set ℓ} → Translatable (Discr A)
  translated-type {{translate-discr {A = A}}} = A
  translate-term  {{translate-discr {A = A}}} t = t ⟨ tt , tt ⟩'
  translate-back  {{translate-discr {A = A}}} a = discr a
  translate-cong  {{translate-discr {A = A}}} e = eq e tt

  translate-prod : {T : Ty ◇ ℓ}  {{_ : Translatable T}}
                   {S : Ty ◇ ℓ'} {{_ : Translatable S}} →
                   Translatable (T ⊠ S)
  translated-type {{translate-prod {T = T} {S = S}}} = translate-type T × translate-type S
  translate-term  {{translate-prod {T = T} {S = S}}} p = translate-term (fst p) , translate-term (snd p)
  translate-back  {{translate-prod {T = T} {S = S}}} (t , s) = pair (translate-back t) (translate-back s)
  translate-cong  {{translate-prod {T = T} {S = S}}} e = cong₂ _,_ (translate-cong (fst-cong e)) (translate-cong (snd-cong e))

  translate-sum : {T : Ty ◇ ℓ}  {{_ : Translatable T}}
                  {S : Ty ◇ ℓ'} {{_ : Translatable S}} →
                  Translatable (T ⊞ S)
  translated-type {{translate-sum {T = T} {S = S}}} = translate-type T ⊎ translate-type S
  translate-term  {{translate-sum {T = T} {S = S}}} p = map translate-term translate-term (expose-sum-term p)
  translate-back  {{translate-sum {T = T} {S = S}}} (inl t) = inl' (translate-back t)
  translate-back  {{translate-sum {T = T} {S = S}}} (inr s) = inr' (translate-back s)
  translate-cong  {{translate-sum {T = T} {S = S}}} {t = p}{s = q} e with expose-sum-term p | expose-sum-term q | expose-sum-cong e
  ... | inl t1 | inl t2 | inl et = cong inl (translate-cong et)
  ... | inr s1 | inr s2 | inr es = cong inr (translate-cong es)

  translate-func : {T : Ty ◇ ℓ}  {{_ : Translatable T}}
                   {S : Ty ◇ ℓ'} {{_ : Translatable S}} →
                   Translatable (T ⇛ S)
  translated-type {{translate-func {T = T} {S = S}}} = translate-type T → translate-type S
  translate-term  {{translate-func {T = T} {S = S}}} f t = translate-term (app f (translate-back t))
  translate-back  {{translate-func {T = T} {S = S}}} f = lam T {!!}
  translate-cong  {{translate-func {T = T} {S = S}}} ef = funext λ x → translate-cong (app-cong ef ≅ᵗᵐ-refl)



open import Reflection.Naturality
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.Lambda
open import Reflection.Naturality.Instances

nat-sum : Tm {C = ★} ◇ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = nat-elim (Nat' ⇛ Nat')
                   (lamι Nat' (varι 0))
                   (lamι (Nat' ⇛ Nat')
                         (lamι Nat' (suc' (app (varι 1) (varι 0)))))

nat-sum-β : (m n : Tm {C = ★} ◇ Nat') → app (app nat-sum (suc' m)) n ≅ᵗᵐ suc' (app (app nat-sum m) n)
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
open import GuardedRecursion.GuardedStreams using (first-≤; first-≤-refl; paperfolds; fibs)

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

instance
  translate-stream : Translatable Stream'
  translated-type {{translate-stream}} = Stream ℕ
  head (translate-term {{translate-stream}} s) = translate-term (head' $ s)
  tail (translate-term {{translate-stream}} s) = translate-term (tail' $ s)
  translate-back {{translate-stream}} s = MkTm (λ _ _ → MkTm (λ n _ → take (suc n) s)
                                                             (λ m≤n _ → take-first (s≤s m≤n) s))
                                               (λ _ _ → tm-≅-to-≡ (record { eq = λ _ → first-≤-refl }))
  translate-cong {{translate-stream}} = {!!}

paperfolds-stream : Stream ℕ
paperfolds-stream = translate-term (global-tm paperfolds)

fibs-stream : Stream ℕ
fibs-stream = translate-term (global-tm fibs)

private
  fibs-stream-test : take 10 fibs-stream ≡ (1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ [])
  fibs-stream-test = refl

  paperfolds-stream-test : take 10 paperfolds-stream ≡ (1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ [])
  paperfolds-stream-test = refl
