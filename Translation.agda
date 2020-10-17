module Translation where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; map) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums

private
  variable
    ℓc ℓ ℓ' : Level


record Translatable (T : Ty {C = ★} ◇ ℓ) : Set (lsuc ℓ) where
  field
    translated-type : Set ℓ
    translate-term  : Tm ◇ T → translated-type
    translate-back  : translated-type → Tm ◇ T

open Translatable {{...}} public

translate-type : (T : Ty {C = ★} ◇ ℓ) → {{Translatable T}} → Set ℓ
translate-type T = translated-type {T = T}

expose-sum-term : {A : Ty {C = ★} ◇ ℓ} {B : Ty ◇ ℓ'} →
                  Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
expose-sum-term {A = A}{B = B} p with p ⟨ tt , tt ⟩'
... | inl a = inl (MkTm (λ { tt tt → a }) (λ { tt refl → morph-id A a }))
... | inr b = inr (MkTm (λ { tt tt → b }) (λ { tt refl → morph-id B b }))

instance
  translate-discr : {A : Set ℓ} → Translatable (Discr A)
  translated-type {{translate-discr {A = A}}} = A
  translate-term  {{translate-discr {A = A}}} t = t ⟨ tt , tt ⟩'
  translate-back  {{translate-discr {A = A}}} a = discr a

  translate-prod : {T : Ty ◇ ℓ}  {{_ : Translatable T}}
                   {S : Ty ◇ ℓ'} {{_ : Translatable S}} →
                   Translatable (T ⊠ S)
  translated-type {{translate-prod {T = T} {S = S}}} = translate-type T × translate-type S
  translate-term  {{translate-prod {T = T} {S = S}}} p = translate-term (fst p) , translate-term (snd p)
  translate-back  {{translate-prod {T = T} {S = S}}} (t , s) = pair (translate-back t) (translate-back s)

  translate-sum : {T : Ty ◇ ℓ}  {{_ : Translatable T}}
                  {S : Ty ◇ ℓ'} {{_ : Translatable S}} →
                  Translatable (T ⊞ S)
  translated-type {{translate-sum {T = T} {S = S}}} = translate-type T ⊎ translate-type S
  translate-term  {{translate-sum {T = T} {S = S}}} p = map translate-term translate-term (expose-sum-term p)
  translate-back  {{translate-sum {T = T} {S = S}}} (inl t) = inl' (translate-back t)
  translate-back  {{translate-sum {T = T} {S = S}}} (inr s) = inr' (translate-back s)

  translate-func : {T : Ty ◇ ℓ}  {{_ : Translatable T}}
                   {S : Ty ◇ ℓ'} {{_ : Translatable S}} →
                   Translatable (T ⇛ S)
  translated-type {{translate-func {T = T} {S = S}}} = translate-type T → translate-type S
  translate-term  {{translate-func {T = T} {S = S}}} f t = translate-term (app f (translate-back t))
  translate-back  {{translate-func {T = T} {S = S}}} f = lam T {!!}



open import Reflection.Naturality
open import Reflection.NaturalityTactic

nat-sum : Tm {C = ★} ◇ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = nat-elim (Nat' ⇛ Nat')
                   (lamι Nat' (varι 0))
                   (lamι (Nat' ⇛ Nat')
                         (lamι Nat' (app (varι 1) (suc' (varι 0)))))

open import Data.Nat

_+'_ : ℕ → ℕ → ℕ
_+'_ = translate-term nat-sum

test : 6 +' 3 ≡ 9
test = refl
