--------------------------------------------------
-- Extracting embedded (semantic) terms in base category ★ to Agda
--------------------------------------------------

module Extraction where

open import Function using (_∘_)
open import Data.Nat
open import Data.Product using (_×_) renaming (_,_ to [_,_])
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Constant
open import Model.Type.Function
open import Model.Type.Product
open import Model.Type.Sum


--------------------------------------------------
-- Definition of the Extractable type class

record Extractable (T : ClosedTy ★) : Set₁ where
  field
    translated-type : Set
    extract-term : Tm ◇ T → translated-type
    embed-term : translated-type → Tm ◇ T

open Extractable {{...}} public

translate-type : (T : ClosedTy ★) → {{Extractable T}} → Set
translate-type T = translated-type {T = T}


--------------------------------------------------
-- Instances of Extractable for Sikkel's built-in types & type
-- constructors (constant types, products, sums, functions)

instance
  extract-const : {A : Set} → Extractable (Const A)
  translated-type {{extract-const {A = A}}} = A
  extract-term {{extract-const {A = A}}} t = t ⟨ tt , tt ⟩'
  embed-term {{extract-const {A = A}}} a = const a

  extract-prod : {T : ClosedTy ★} {{_ : Extractable T}}
                 {S : ClosedTy ★} {{_ : Extractable S}} →
                 Extractable (T ⊠ S)
  translated-type {{extract-prod {T = T} {S = S}}} = translate-type T × translate-type S
  extract-term {{extract-prod {T = T} {S = S}}} p = [ extract-term (fst $ p) , extract-term (snd $ p) ]
  embed-term {{extract-prod {T = T} {S = S}}} [ t , s ] = pair $ embed-term t $ embed-term s

expose-sum-term : {A : Ty {C = ★} ◇} {B : Ty ◇} →
                  Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
expose-sum-term {A = A}{B = B} p with p ⟨ tt , tt ⟩'
... | inj₁ a = inj₁ (MkTm (λ { tt tt → a }) (λ { tt refl → ty-id A }))
... | inj₂ b = inj₂ (MkTm (λ { tt tt → b }) (λ { tt refl → ty-id B }))

instance
  extract-sum : {T : ClosedTy ★} {{_ : Extractable T}}
                {S : ClosedTy ★} {{_ : Extractable S}} →
                Extractable (T ⊞ S)
  translated-type {{extract-sum {T = T} {S = S}}} = translate-type T ⊎ translate-type S
  extract-term {{extract-sum {T = T} {S = S}}} p = map extract-term extract-term (expose-sum-term p)
  embed-term {{extract-sum {T = T} {S = S}}} (inj₁ t) = inl (embed-term t)
  embed-term {{extract-sum {T = T} {S = S}}} (inj₂ s) = inr (embed-term s)

-- A term in the empty context in mode ★ is nothing more than an Agda value.
to-★-◇-term : {T : Ty {C = ★} ◇} → T ⟨ tt , tt ⟩ → Tm ◇ T
to-★-◇-term t ⟨ _ , _ ⟩' = t
Tm.naturality (to-★-◇-term {T = T} t) _ refl = ty-id T

-- A function in the empty context in mode ★ is nothing more than an Agda function.
func-★-◇ : {T : Ty {C = ★} ◇} {S : Ty {C = ★} ◇} →
           (Tm ◇ T → Tm ◇ S) → Tm ◇ (T ⇛ S)
(func-★-◇ {T = T} f ⟨ _ , _ ⟩') $⟨ _ , refl ⟩ t = f (to-★-◇-term t) ⟨ tt , tt ⟩'
PshFun.naturality (func-★-◇ {T = T}{S = S} f ⟨ _ , _ ⟩') {ρ-xy = _} {eγ-zy = refl} {refl} {t} =
  trans (cong (λ x → f (to-★-◇-term x) ⟨ tt , tt ⟩') (ty-id T)) (sym (ty-id S))
Tm.naturality (func-★-◇ f) _ refl = to-pshfun-eq (λ { _ refl _ → refl })

instance
  extract-func : {T : ClosedTy ★} {{_ : Extractable T}}
                 {S : ClosedTy ★} {{_ : Extractable S}} →
                 Extractable (T ⇛ S)
  translated-type {{extract-func {T = T} {S = S}}} = translate-type T → translate-type S
  extract-term {{extract-func {T = T} {S = S}}} f t = extract-term (app f (embed-term t))
  embed-term {{extract-func {T = T} {S = S}}} f = func-★-◇ (embed-term ∘ f ∘ extract-term)
