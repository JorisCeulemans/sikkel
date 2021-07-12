--------------------------------------------------
-- Extracting embedded terms in mode ★ to Agda
--------------------------------------------------

module Translation where

open import Function using (_∘_)
open import Data.Nat
open import Data.Product using (_×_) renaming (_,_ to [_,_])
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.Sum.Relation.Binary.Pointwise
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
open import Types.Instances
open import Reflection.Tactic.Lambda


--------------------------------------------------
-- Definition of the Translatable type class

record Translatable (T : ClosedType ★) : Set₁ where
  field
    translated-type : Set
    translate-term  : Tm ◇ T → translated-type
    translate-back  : translated-type → Tm ◇ T

open Translatable {{...}} public

translate-type : (T : ClosedType ★) → {{Translatable T}} → Set
translate-type T = translated-type {T = T}


--------------------------------------------------
-- Instances of Translatable for Sikkel's built-in types & type
-- constructors (discrete types, products, sums, functions)

instance
  translate-discr : {A : Set} → Translatable (Discr A)
  translated-type {{translate-discr {A = A}}} = A
  translate-term  {{translate-discr {A = A}}} t = t ⟨ tt , tt ⟩'
  translate-back  {{translate-discr {A = A}}} a = discr a

  translate-prod : {T : ClosedType ★} {{_ : Translatable T}}
                   {S : ClosedType ★} {{_ : Translatable S}} →
                   Translatable (T ⊠ S)
  translated-type {{translate-prod {T = T} {S = S}}} = translate-type T × translate-type S
  translate-term  {{translate-prod {T = T} {S = S}}} p = [ translate-term (fst p) , translate-term (snd p) ]
  translate-back  {{translate-prod {T = T} {S = S}}} [ t , s ] = pair (translate-back t) (translate-back s)

expose-sum-term : {A : Ty {C = ★} ◇} {B : Ty ◇} →
                  Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
expose-sum-term {A = A}{B = B} p with p ⟨ tt , tt ⟩'
... | inj₁ a = inj₁ (MkTm (λ { tt tt → a }) (λ { tt refl → ty-id A }))
... | inj₂ b = inj₂ (MkTm (λ { tt tt → b }) (λ { tt refl → ty-id B }))

instance
  translate-sum : {T : ClosedType ★} {{_ : Translatable T}}
                  {S : ClosedType ★} {{_ : Translatable S}} →
                  Translatable (T ⊞ S)
  translated-type {{translate-sum {T = T} {S = S}}} = translate-type T ⊎ translate-type S
  translate-term  {{translate-sum {T = T} {S = S}}} p = map translate-term translate-term (expose-sum-term p)
  translate-back  {{translate-sum {T = T} {S = S}}} (inj₁ t) = inl (translate-back t)
  translate-back  {{translate-sum {T = T} {S = S}}} (inj₂ s) = inr (translate-back s)

-- A term in the empty context in mode ★ is nothing more than an Agda value.
to-★-◇-term : {T : Ty {C = ★} ◇} → T ⟨ tt , tt ⟩ → Tm ◇ T
to-★-◇-term t ⟨ _ , _ ⟩' = t
Tm.naturality (to-★-◇-term {T = T} t) _ refl = ty-id T

-- A function in the empty context in mode ★ is nothing more than an Agda function.
func-★-◇ : {T : Ty {C = ★} ◇} {S : Ty {C = ★} ◇} →
           (Tm ◇ T → Tm ◇ S) → Tm ◇ (T ⇛ S)
(func-★-◇ {T = T} f ⟨ _ , _ ⟩') $⟨ _ , refl ⟩ t = f (to-★-◇-term t) ⟨ tt , tt ⟩'
PresheafFunc.naturality (func-★-◇ {T = T}{S = S} f ⟨ _ , _ ⟩') {ρ-xy = _} {eγ-zy = refl} {refl} {t} =
  trans (cong (λ x → f (to-★-◇-term x) ⟨ tt , tt ⟩') (ty-id T)) (sym (ty-id S))
Tm.naturality (func-★-◇ f) _ refl = to-pshfun-eq (λ { _ refl _ → refl })

instance
  translate-func : {T : ClosedType ★} {{_ : Translatable T}}
                   {S : ClosedType ★} {{_ : Translatable S}} →
                   Translatable (T ⇛ S)
  translated-type {{translate-func {T = T} {S = S}}} = translate-type T → translate-type S
  translate-term  {{translate-func {T = T} {S = S}}} f t = translate-term (app f (translate-back t))
  translate-back  {{translate-func {T = T} {S = S}}} f = func-★-◇ (translate-back ∘ f ∘ translate-term)


--------------------------------------------------
-- Example: translating addition of natural numbers from Sikkel to Agda

private
  -- Definition of addition in Sikkel using the recursion principle for Nat'.
  nat-sum' : Tm {C = ★} ◇ (Nat' ⇛ Nat' ⇛ Nat')
  nat-sum' = nat-elim (Nat' ⇛ Nat')
                      (lamι[ "n" ∈ Nat' ] varι "n")
                      (lamι[ "f" ∈ Nat' ⇛ Nat' ] lamι[ "n" ∈ Nat' ] suc' $ (varι "f" $ varι "n"))

  _+'_ : ℕ → ℕ → ℕ
  _+'_ = translate-term nat-sum'

  test : 6 +' 3 ≡ 9
  test = refl
