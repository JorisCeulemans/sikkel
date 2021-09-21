--------------------------------------------------
-- An example of representation independence using
-- binary parametricity
--------------------------------------------------

module Parametricity.Binary.IntegerExample where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Instances
open import Modalities
open import Reflection.Tactic.Lambda
open import Translation

open import Parametricity.Binary.TypeSystem

private
  variable
    Γ : Ctx ⋀


record IntStructure {C} (A : ClosedType C) {{_ : IsClosedNatural A}} : Set₁ where
  field
    prim-add : ∀ {Γ} → Tm (Γ ,, A ,, A) A
    prim-negate : ∀ {Γ} → Tm (Γ ,, A) A

  add : ∀ {Γ} → Tm Γ (A ⇛ A ⇛ A)
  add = lamι A (lamι A prim-add)

  negate : ∀ {Γ} → Tm Γ (A ⇛ A)
  negate = lamι A prim-negate

open IntStructure {{...}}

subtract : ∀ {C Γ} {A : ClosedType C} {{_ : IsClosedNatural A}} {{_ : IntStructure A}} →
           Tm Γ (A ⇛ A ⇛ A)
subtract {A = A} = lamι[ "i" ∈ A ] lamι[ "j" ∈ A ] add $ varι "i" $ (negate $ varι "j")


instance
  ℤ-is-int : IntStructure ℤ
  prim-add {{ℤ-is-int}} = from-rel2 _+D_ _+S_ +-preserves-∼
  prim-negate {{ℤ-is-int}} = from-rel1 negateD negateS negate-preserves-∼

module _ (i : Tm ◇ ℤ) where
  translate-i1 : DiffNat
  translate-i1 = i ⟨ left , _ ⟩'

  translate-i2 : SignNat
  translate-i2 = i ⟨ right , _ ⟩'

  translations-related : translate-i1 ∼ translate-i2
  translations-related with i ⟨ relation , _ ⟩' | Tm.naturality i left-rel refl | Tm.naturality i right-rel refl
  translations-related | [ _ , r ] | refl | refl = r


subtract★-left : {Γ : Ctx ★} → Tm Γ (forget-right-ty ℤ ⇛ forget-right-ty ℤ ⇛ forget-right-ty ℤ)
subtract★-left = lamι[ "i" ∈ forget-right-ty ℤ ] lamι[ "j" ∈ forget-right-ty ℤ ]
                 subtract ⟨$- forget-right ⟩ varι "i" ⊛⟨ forget-right ⟩ varι "j"

subtract★-right : {Γ : Ctx ★} → Tm Γ (forget-left-ty ℤ ⇛ forget-left-ty ℤ ⇛ forget-left-ty ℤ)
subtract★-right = lamι[ "i" ∈ forget-left-ty ℤ ] lamι[ "j" ∈ forget-left-ty ℤ ]
                  subtract ⟨$- forget-left ⟩ varι "i" ⊛⟨ forget-left ⟩ varι "j"

instance
  forget-right-rel : {A B : Set} {R : REL A B 0ℓ} → Translatable (forget-right-ty (FromRel A B R))
  Translatable.translated-type (forget-right-rel {A = A}) = A
  Translatable.translate-term forget-right-rel t = t ⟨ tt , tt ⟩'
  Translatable.translate-back forget-right-rel a = MkTm (λ _ _ → a) (λ _ _ → refl)

  forget-left-rel : {A B : Set} {R : REL A B 0ℓ} → Translatable (forget-left-ty (FromRel A B R))
  Translatable.translated-type (forget-left-rel {B = B}) = B
  Translatable.translate-term forget-left-rel t = t ⟨ tt , tt ⟩'
  Translatable.translate-back forget-left-rel b = MkTm (λ _ _ → b) (λ _ _ → refl)

subtract-DiffNat : DiffNat → DiffNat → DiffNat
subtract-DiffNat = translate-term subtract★-left

subtract-SignNat : SignNat → SignNat → SignNat
subtract-SignNat = translate-term subtract★-right

subtract-ℤ : Tm Γ (ℤ ⇛ ℤ ⇛ ℤ)
subtract-ℤ = subtract

subtract-preserves-∼ : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) subtract-DiffNat subtract-SignNat
subtract-preserves-∼ {d1}{s1} r1 {d2}{s2} r2 = proj₂ (
  (subtract-ℤ {Γ = ◇} €⟨ relation , tt ⟩ [ [ d1 , s1 ] , r1 ]) $⟨ relation-id , refl ⟩ [ [ d2 , s2 ] , r2 ])
