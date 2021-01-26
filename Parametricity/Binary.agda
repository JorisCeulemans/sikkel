{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- An example of representation independence using
-- binary parametricity
--------------------------------------------------

module Parametricity.Binary where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Function using (id; _∘_)
open import Level using (Level; 0ℓ; _⊔_; Setω)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Reflection.Naturality
open import Reflection.Naturality.Instances
open import Reflection.SubstitutionSequence
open import Reflection.Tactic.Lambda

private
  variable
    ℓ ℓ' : Level
    Γ : Ctx ⋀ ℓ


--------------------------------------------------
-- Constructing an embedded type in base category ⋀
-- using two Agda types and a relation

PrimFromRel : (A B : Set ℓ) (R : REL A B ℓ) → Ty {C = ⋀} ◇ ℓ
type (PrimFromRel A B R) left  _ = A
type (PrimFromRel A B R) right _ = B
type (PrimFromRel A B R) relation _ = Σ[ p ∈ A × B ] uncurry R p
morph (PrimFromRel A B R) left-id  _ = id
morph (PrimFromRel A B R) right-id _ = id
morph (PrimFromRel A B R) relation-id _ = id
morph (PrimFromRel A B R) left-rel  _ = proj₁ ∘ proj₁
morph (PrimFromRel A B R) right-rel _ = proj₂ ∘ proj₁
morph-cong (PrimFromRel A B R) refl {eγ = refl}{eγ' = refl} = refl
morph-id (PrimFromRel A B R) {x = left}  _ = refl
morph-id (PrimFromRel A B R) {x = right} _ = refl
morph-id (PrimFromRel A B R) {x = relation} _ = refl
morph-comp (PrimFromRel A B R) left-id  g refl refl _ = refl
morph-comp (PrimFromRel A B R) right-id g refl refl _ = refl
morph-comp (PrimFromRel A B R) relation-id g refl refl _ = refl
morph-comp (PrimFromRel A B R) left-rel  relation-id _ _ _ = refl
morph-comp (PrimFromRel A B R) right-rel relation-id _ _ _ = refl

FromRel : (A B : Set ℓ) (R : REL A B ℓ) → NullaryTypeOp ⋀ ℓ
FromRel A B R {Γ = Γ} = PrimFromRel A B R [ !◇ Γ ]

instance
  fromrel-natural : {A B : Set ℓ} {R : REL A B ℓ} → IsNullaryNatural (FromRel A B R)
  natural-nul {{fromrel-natural}} σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) (PrimFromRel _ _ _) (◇-terminal _ _ _)

from-rel : {A B : Set ℓ} {R : REL A B ℓ} (a : A) (b : B) → R a b → Tm Γ (FromRel A B R)
term (from-rel a b r) left  _ = a
term (from-rel a b r) right _ = b
term (from-rel a b r) relation _ = [ [ a , b ] , r ]
Tm.naturality (from-rel a b r) left-id  _ = refl
Tm.naturality (from-rel a b r) right-id _ = refl
Tm.naturality (from-rel a b r) relation-id _ = refl
Tm.naturality (from-rel a b r) left-rel  _ = refl
Tm.naturality (from-rel a b r) right-rel _ = refl

infixr 0 _⟨→⟩_
_⟨→⟩_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
        REL A C ℓ → REL B D ℓ' → REL (A → B) (C → D) _
(R ⟨→⟩ S) f g = ∀ {a c} → R a c → S (f a) (g c)

from-rel1 : {A1 B1 : Set ℓ}  {R1 : REL A1 B1 ℓ}
            {A2 B2 : Set ℓ'} {R2 : REL A2 B2 ℓ'}
            (f : A1 → A2) (g : B1 → B2) → (R1 ⟨→⟩ R2) f g →
            Tm (Γ ,, FromRel A1 B1 R1) (FromRel A2 B2 R2)
term (from-rel1 f g h) left  [ _ , a ] = f a
term (from-rel1 f g h) right [ _ , b ] = g b
term (from-rel1 f g h) relation [ _ , [ [ a , b ] , r ] ] = [ [ f a , g b ] , h r ]
Tm.naturality (from-rel1 f g h) left-id refl = refl
Tm.naturality (from-rel1 f g h) right-id refl = refl
Tm.naturality (from-rel1 f g h) relation-id refl = refl
Tm.naturality (from-rel1 f g h) left-rel refl = refl
Tm.naturality (from-rel1 f g h) right-rel refl = refl

from-rel2 : ∀ {ℓ1 ℓ2 ℓ3}
            {A1 B1 : Set ℓ1} {R1 : REL A1 B1 ℓ1}
            {A2 B2 : Set ℓ2} {R2 : REL A2 B2 ℓ2}
            {A3 B3 : Set ℓ3} {R3 : REL A3 B3 ℓ3}
            (f : A1 → A2 → A3) (g : B1 → B2 → B3) → (R1 ⟨→⟩ R2 ⟨→⟩ R3) f g →
            Tm (Γ ,, FromRel A1 B1 R1 ⊠ FromRel A2 B2 R2) (FromRel A3 B3 R3)
term (from-rel2 f g h) left  [ _ , [ a1 , a2 ] ] = f a1 a2
term (from-rel2 f g h) right [ _ , [ b1 , b2 ] ] = g b1 b2
term (from-rel2 f g h) relation [ _ , [ [ [ a1 , b1 ] , r1 ] , [ [ a2 , b2 ] , r2 ] ] ] = [ [ f a1 a2 , g b1 b2 ] , h r1 r2 ]
Tm.naturality (from-rel2 f g h) left-id  refl = refl
Tm.naturality (from-rel2 f g h) right-id refl = refl
Tm.naturality (from-rel2 f g h) relation-id refl = refl
Tm.naturality (from-rel2 f g h) left-rel  refl = refl
Tm.naturality (from-rel2 f g h) right-rel refl = refl


--------------------------------------------------
-- Example: types representing integers

record IntStructure (A : NullaryTypeOp ⋀ ℓ) {{_ : IsNullaryNatural A}} : Setω where
  field
    prim-add : Tm (Γ ,, A ⊠ A) A
    prim-negate : Tm (Γ ,, A) A

  add : Tm Γ (A ⊠ A ⇛ A)
  add = lamι (A ⊠ A) prim-add

  negate : Tm Γ (A ⇛ A)
  negate = lamι A prim-negate

open IntStructure {{...}}

subtract : {A : NullaryTypeOp ⋀ ℓ} {{_ : IsNullaryNatural A}} {{_ : IntStructure A}} →
           Tm Γ (A ⇛ A ⇛ A)
subtract {A = A} = nlamι[ "i" ∈ A ] nlamι[ "j" ∈ A ] add $ pair (nvarι "i") (negate $ nvarι "j")

data Sign : Set where
  pos neg : Sign

flipSign : Sign → Sign
flipSign pos = neg
flipSign neg = pos

DiffInt : Set
DiffInt = ℕ × ℕ

SignNat : Set
SignNat = Sign × ℕ

infix 3 _∼_

data _∼_ : REL DiffInt SignNat 0ℓ where
  pos-zero : ∀ {n} → [ n , 0 ] ∼ [ pos , n ]
  neg-zero : ∀ {n} → [ 0 , n ] ∼ [ neg , n ]
  diff-suc : ∀ {m n j} → [ m , n ] ∼ j → [ suc m , suc n ] ∼ j

PrimIntRep : Ty {C = ⋀} ◇ 0ℓ
PrimIntRep = PrimFromRel DiffInt SignNat _∼_

IntRep : NullaryTypeOp ⋀ 0ℓ
IntRep = FromRel DiffInt SignNat _∼_

_+D_ : DiffInt → DiffInt → DiffInt
[ m1 , n1 ] +D [ m2 , n2 ] = [ m1 + m2 , n1 + n2 ]

negateD : DiffInt → DiffInt
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
  intrep-is-int : IntStructure IntRep
  prim-add {{intrep-is-int}} = from-rel2 _+D_ _+S_ +-preserves-∼
  prim-negate {{intrep-is-int}} = from-rel1 negateD negateS negate-preserves-∼

module _ (i : Tm ◇ IntRep) where
  translate-i1 : DiffInt
  translate-i1 = i ⟨ left , _ ⟩'

  translate-i2 : SignNat
  translate-i2 = i ⟨ right , _ ⟩'

  translations-related : translate-i1 ∼ translate-i2
  translations-related with i ⟨ relation , _ ⟩' | Tm.naturality i left-rel refl | Tm.naturality i right-rel refl
  translations-related | [ _ , r ] | refl | refl = r


open import Data.Unit
open import Data.Empty.Polymorphic

just-left : Ctx ★ ℓ → Ctx ⋀ ℓ
set (just-left Γ) left = Γ ⟨ tt ⟩
set (just-left Γ) right = ⊥
set (just-left Γ) relation = ⊥
rel (just-left Γ) left-id = id
rel (just-left Γ) right-id = id
rel (just-left Γ) relation-id = id
rel (just-left Γ) left-rel = ⊥-elim
rel (just-left Γ) right-rel = id
rel-id (just-left Γ) {x = left} _ = refl
rel-comp (just-left Γ) left-id g _ = refl
rel-comp (just-left Γ) right-id g _ = refl
rel-comp (just-left Γ) relation-id g _ = refl
rel-comp (just-left Γ) left-rel relation-id _ = refl
rel-comp (just-left Γ) right-rel relation-id _ = refl

forget-right : {Γ : Ctx ★ ℓ} → Ty (just-left Γ) ℓ' → Ty Γ ℓ'
type (forget-right T) tt γ = T ⟨ left , γ ⟩
morph (forget-right {Γ = Γ} T) tt eγ = T ⟪ left-id , trans (sym (rel-id Γ _)) eγ ⟫_
morph-cong (forget-right T) refl {eγ = refl} {eγ' = refl} = refl
morph-id (forget-right T) t = trans (morph-cong T refl) (morph-id T t)
morph-comp (forget-right T) _ _ _ _ _ = sym (morph-cong-2-1 T refl)

module _ {Γ : Ctx ★ ℓ} {T : Ty (just-left Γ) ℓ'} where
  forget-right-intro : Tm (just-left Γ) T → Tm Γ (forget-right T)
  term (forget-right-intro t) _ γ = t ⟨ left , γ ⟩'
  Tm.naturality (forget-right-intro t) tt eγ = Tm.naturality t left-id _

  forget-right-elim : Tm Γ (forget-right T) → Tm (just-left Γ) T
  term (forget-right-elim t) left γ = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-right-elim t) left-id eγ = trans (morph-cong T refl) (Tm.naturality t tt (trans (rel-id Γ _) eγ))

just-right : Ctx ★ ℓ → Ctx ⋀ ℓ
set (just-right Γ) left = ⊥
set (just-right Γ) right = Γ ⟨ tt ⟩
set (just-right Γ) relation = ⊥
rel (just-right Γ) left-id = id
rel (just-right Γ) right-id = id
rel (just-right Γ) relation-id = id
rel (just-right Γ) left-rel = id
rel (just-right Γ) right-rel = ⊥-elim
rel-id (just-right Γ) {x = right} _ = refl
rel-comp (just-right Γ) left-id g _ = refl
rel-comp (just-right Γ) right-id g _ = refl
rel-comp (just-right Γ) relation-id g _ = refl
rel-comp (just-right Γ) left-rel relation-id _ = refl
rel-comp (just-right Γ) right-rel relation-id _ = refl

forget-left : {Γ : Ctx ★ ℓ} → Ty (just-right Γ) ℓ' → Ty Γ ℓ'
type (forget-left T) tt γ = T ⟨ right , γ ⟩
morph (forget-left {Γ = Γ} T) tt eγ = T ⟪ right-id , trans (sym (rel-id Γ _)) eγ ⟫_
morph-cong (forget-left T) refl {eγ = refl} {eγ' = refl} = refl
morph-id (forget-left T) t = trans (morph-cong T refl) (morph-id T t)
morph-comp (forget-left T) _ _ _ _ _ = sym (morph-cong-2-1 T refl)

module _ {Γ : Ctx ★ ℓ} {T : Ty (just-right Γ) ℓ'} where
  forget-left-intro : Tm (just-right Γ) T → Tm Γ (forget-left T)
  term (forget-left-intro t) _ γ = t ⟨ right , γ ⟩'
  Tm.naturality (forget-left-intro t) tt eγ = Tm.naturality t right-id _

  forget-left-elim : Tm Γ (forget-left T) → Tm (just-right Γ) T
  term (forget-left-elim t) right γ = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-left-elim t) right-id eγ = trans (morph-cong T refl) (Tm.naturality t tt (trans (rel-id Γ _) eγ))
