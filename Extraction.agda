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

open Extractable public


--------------------------------------------------
-- Instances of Extractable for Sikkel's built-in types & type
-- constructors (constant types, products, sums, functions)

extract-const : {A : Set} → Extractable (Const A)
translated-type (extract-const {A = A}) = A
extract-term (extract-const {A = A}) t = t ⟨ tt , tt ⟩'
embed-term (extract-const {A = A}) a = const a

extract-prod : {T S : ClosedTy ★} → Extractable T → Extractable S → Extractable (T ⊠ S)
translated-type (extract-prod exT exS) = translated-type exT × translated-type exS
extract-term (extract-prod exT exS) p = [ extract-term exT (fst p) , extract-term exS (snd p) ]
embed-term (extract-prod exT exS) [ t , s ] = pair (embed-term exT t) (embed-term exS s)

expose-sum-term : {A : Ty {C = ★} ◇} {B : Ty ◇} →
                  Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
expose-sum-term {A = A}{B = B} p with p ⟨ tt , tt ⟩'
... | inj₁ a = inj₁ (MkTm (λ { tt tt → a }) (λ { tt refl → ty-id A }))
... | inj₂ b = inj₂ (MkTm (λ { tt tt → b }) (λ { tt refl → ty-id B }))

extract-sum : {T S : ClosedTy ★} → Extractable T → Extractable S → Extractable (T ⊞ S)
translated-type (extract-sum exT exS) = translated-type exT ⊎ translated-type exS
extract-term (extract-sum exT exS) p = map (extract-term exT) (extract-term exS) (expose-sum-term p)
embed-term (extract-sum exT exS) (inj₁ t) = inl (embed-term exT t)
embed-term (extract-sum exT exS) (inj₂ s) = inr (embed-term exS s)

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

extract-func : {T S : ClosedTy ★} → Extractable T → Extractable S → Extractable (T ⇛ S)
translated-type (extract-func exT exS) = translated-type exT → translated-type exS
extract-term (extract-func exT exS) f t = extract-term exS (app f (embed-term exT t))
embed-term (extract-func exT exS) f = func-★-◇ (embed-term exS ∘ f ∘ extract-term exT)
