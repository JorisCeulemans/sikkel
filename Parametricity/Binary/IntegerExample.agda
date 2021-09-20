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
open import Translation2

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

data Sign : Set where
  pos neg : Sign

flipSign : Sign → Sign
flipSign pos = neg
flipSign neg = pos

DiffNat : Set
DiffNat = ℕ × ℕ

SignNat : Set
SignNat = Sign × ℕ

infix 3 _∼_

data _∼_ : REL DiffNat SignNat 0ℓ where
  pos-zero : ∀ {n} → [ n , 0 ] ∼ [ pos , n ]
  neg-zero : ∀ {n} → [ 0 , n ] ∼ [ neg , n ]
  diff-suc : ∀ {m n j} → [ m , n ] ∼ j → [ suc m , suc n ] ∼ j

Primℤ : Ty {C = ⋀} ◇
Primℤ = PrimFromRel DiffNat SignNat _∼_

ℤ : ClosedType ⋀
ℤ = FromRel DiffNat SignNat _∼_

_+D_ : DiffNat → DiffNat → DiffNat
[ m1 , n1 ] +D [ m2 , n2 ] = [ m1 + m2 , n1 + n2 ]

negateD : DiffNat → DiffNat
negateD [ m , n ] = [ n , m ]

_-_ : ℕ → ℕ → SignNat
m     - zero  = [ pos , m ]
zero  - n     = [ neg , n ]
suc m - suc n = m - n

_+S_ : SignNat → SignNat → SignNat
[ pos , m ] +S [ pos , n ] = [ pos , m + n ]
[ pos , m ] +S [ neg , n ] = m - n
[ neg , m ] +S [ pos , n ] = n - m
[ neg , m ] +S [ neg , n ] = [ neg , m + n ]

negateS : SignNat → SignNat
negateS = map₁ flipSign

negate-preserves-∼ : (_∼_ ⟨→⟩ _∼_) negateD negateS
negate-preserves-∼ pos-zero = neg-zero
negate-preserves-∼ neg-zero = pos-zero
negate-preserves-∼ (diff-suc r) = diff-suc (negate-preserves-∼ r)

difference-∼ : ∀ m n → [ m , n ] ∼ m - n
difference-∼ zero    zero    = pos-zero
difference-∼ zero    (suc n) = neg-zero
difference-∼ (suc m) zero    = pos-zero
difference-∼ (suc m) (suc n) = diff-suc (difference-∼ m n)

+-preserves-∼ : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) _+D_ _+S_
+-preserves-∼  pos-zero       pos-zero = pos-zero
+-preserves-∼ (pos-zero {m}) (neg-zero {n}) rewrite +-identityʳ m = difference-∼ m n
+-preserves-∼ (pos-zero {m}) (diff-suc {n} r2) rewrite +-suc m n = diff-suc (+-preserves-∼ pos-zero r2)
+-preserves-∼ (neg-zero {m}) (pos-zero {n}) rewrite +-identityʳ m = difference-∼ n m
+-preserves-∼  neg-zero       neg-zero = neg-zero
+-preserves-∼ (neg-zero {m}) (diff-suc {_}{n} r2) rewrite +-suc m n = diff-suc (+-preserves-∼ neg-zero r2)
+-preserves-∼ (diff-suc r1)   r2 = diff-suc (+-preserves-∼ r1 r2)

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

-- instance
--   forget-right-rel : {A B : Set} {R : REL A B 0ℓ} → Translatable (forget-right-ty (FromRel A B R))
--   Translatable.translated-type (forget-right-rel {A = A}) = A
--   Translatable.translate-term forget-right-rel t = t ⟨ tt , tt ⟩'
--   Translatable.translate-back forget-right-rel a = MkTm (λ _ _ → a) (λ _ _ → refl)

--   forget-left-rel : {A B : Set} {R : REL A B 0ℓ} → Translatable (forget-left-ty (FromRel A B R))
--   Translatable.translated-type (forget-left-rel {B = B}) = B
--   Translatable.translate-term forget-left-rel t = t ⟨ tt , tt ⟩'
--   Translatable.translate-back forget-left-rel b = MkTm (λ _ _ → b) (λ _ _ → refl)

-- subtract-DiffNat : DiffNat → DiffNat → DiffNat
-- subtract-DiffNat = translate-term subtract★-left

-- subtract-SignNat : SignNat → SignNat → SignNat
-- subtract-SignNat = translate-term subtract★-right

instance
  translatable-FromRel : {A B : Set} {R : REL A B 0ℓ} → Translatable (FromRel A B R)
  Translatable.translated-type (translatable-FromRel {A} {B} {R}) {x} xF = PrimFromRel A B R ⟨ x , _ ⟩
  Translatable.translate-term translatable-FromRel {x} xF r = r
  Translatable.translate-back translatable-FromRel {x} xF r = r

subtract-ℤ : Tm Γ (ℤ ⇛ ℤ ⇛ ℤ)
subtract-ℤ = subtract

subtract-Test : Tm ◇ (forget-left-ty (ℤ ⇛ ℤ ⇛ ℤ))
subtract-Test = forget-left-tm subtract-ℤ

subtract-DiffNat : DiffNat → DiffNat → DiffNat
subtract-DiffNat = translate-term {C = ⋀} {T = (ℤ ⇛ ℤ ⇛ ℤ)} {x = left} (λ { [ .left , left-id ] → refl}) (Tm.term (subtract-ℤ {Γ = ◇}) left tt)

subtract-SignNat : SignNat → SignNat → SignNat
subtract-SignNat = translate-term {C = ⋀} {T = (ℤ ⇛ ℤ ⇛ ℤ)} {x = right} (λ { [ .right , right-id ] → refl}) (Tm.term (subtract-ℤ {Γ = ◇}) right tt)

subtract-preserves-∼ : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) subtract-DiffNat subtract-SignNat
subtract-preserves-∼ r1 r2 = proj₂ (
  (subtract-ℤ {Γ = ◇} €⟨ relation , tt ⟩ [ _ , r1 ]) $⟨ relation-id , refl ⟩ [ _ , r2 ])
