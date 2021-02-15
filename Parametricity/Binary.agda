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
open import Relation.Binary hiding (_⇒_)
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
    Γ : Ctx ⋀


--------------------------------------------------
-- Constructing an embedded type in base category ⋀
-- using two Agda types and a relation

PrimFromRel : (A B : Set) (R : REL A B 0ℓ) → Ty {C = ⋀} ◇
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

FromRel : (A B : Set) (R : REL A B 0ℓ) → NullaryTypeOp ⋀
FromRel A B R {Γ = Γ} = PrimFromRel A B R [ !◇ Γ ]

instance
  fromrel-natural : {A B : Set} {R : REL A B 0ℓ} → IsNullaryNatural (FromRel A B R)
  natural-nul {{fromrel-natural}} σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) (PrimFromRel _ _ _) (◇-terminal _ _ _)

from-rel : {A B : Set} {R : REL A B 0ℓ} (a : A) (b : B) → R a b → Tm Γ (FromRel A B R)
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
        REL A C 0ℓ → REL B D 0ℓ → REL (A → B) (C → D) _
(R ⟨→⟩ S) f g = ∀ {a c} → R a c → S (f a) (g c)

from-rel1 : {A1 B1 : Set} {R1 : REL A1 B1 0ℓ}
            {A2 B2 : Set} {R2 : REL A2 B2 0ℓ}
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

from-rel2 : {A1 B1 : Set} {R1 : REL A1 B1 0ℓ}
            {A2 B2 : Set} {R2 : REL A2 B2 0ℓ}
            {A3 B3 : Set} {R3 : REL A3 B3 0ℓ}
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

record IntStructure (A : NullaryTypeOp ⋀) {{_ : IsNullaryNatural A}} : Setω where
  field
    prim-add : Tm (Γ ,, A ⊠ A) A
    prim-negate : Tm (Γ ,, A) A

  add : Tm Γ (A ⊠ A ⇛ A)
  add = lamι (A ⊠ A) prim-add

  negate : Tm Γ (A ⇛ A)
  negate = lamι A prim-negate

open IntStructure {{...}}

subtract : {A : NullaryTypeOp ⋀} {{_ : IsNullaryNatural A}} {{_ : IntStructure A}} →
           Tm Γ (A ⇛ A ⇛ A)
subtract {A = A} = lamι[ "i" ∈ A ] lamι[ "j" ∈ A ] add $ pair (varι "i") (negate $ varι "j")

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

PrimIntRep : Ty {C = ⋀} ◇
PrimIntRep = PrimFromRel DiffInt SignNat _∼_

IntRep : NullaryTypeOp ⋀
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

just-left : Ctx ★ → Ctx ⋀
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

just-left-subst : {Δ : Ctx ★} {Γ : Ctx ★} → Δ ⇒ Γ → just-left Δ ⇒ just-left Γ
func (just-left-subst σ) {x = left}     = func σ
func (just-left-subst σ) {x = right}    = ⊥-elim
func (just-left-subst σ) {x = relation} = ⊥-elim
_⇒_.naturality (just-left-subst σ) {f = left-id} _ = refl

just-left-subst-id : {Γ : Ctx ★} → just-left-subst (id-subst Γ) ≅ˢ id-subst (just-left Γ)
eq just-left-subst-id {x = left} _ = refl

just-left-subst-⊚ : {Δ : Ctx ★} {Γ : Ctx ★} {Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                    just-left-subst (σ ⊚ τ) ≅ˢ just-left-subst σ ⊚ just-left-subst τ
eq (just-left-subst-⊚ σ τ) {x = left} _ = refl

forget-right : {Γ : Ctx ★} → Ty (just-left Γ) → Ty Γ
type (forget-right T) tt γ = T ⟨ left , γ ⟩
morph (forget-right {Γ = Γ} T) tt eγ = T ⟪ left-id , trans (sym (rel-id Γ _)) eγ ⟫_
morph-cong (forget-right T) refl {eγ = refl} {eγ' = refl} = refl
morph-id (forget-right T) t = trans (morph-cong T refl) (morph-id T t)
morph-comp (forget-right T) _ _ _ _ _ = sym (morph-cong-2-1 T refl)

module _ {Γ : Ctx ★} {T : Ty (just-left Γ)} where
  forget-right-intro : Tm (just-left Γ) T → Tm Γ (forget-right T)
  term (forget-right-intro t) _ γ = t ⟨ left , γ ⟩'
  Tm.naturality (forget-right-intro t) tt eγ = Tm.naturality t left-id _

  forget-right-elim : Tm Γ (forget-right T) → Tm (just-left Γ) T
  term (forget-right-elim t) left γ = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-right-elim t) left-id eγ = trans (morph-cong T refl) (Tm.naturality t tt (trans (rel-id Γ _) eγ))

forget-right-natural : {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ)
                       {T : Ty (just-left Γ)} →
                       (forget-right T) [ σ ] ≅ᵗʸ forget-right (T [ just-left-subst σ ])
func (from (forget-right-natural σ)) = id
CwF-Structure.naturality (from (forget-right-natural σ {T = T})) _ = morph-cong T refl
func (to (forget-right-natural σ)) = id
CwF-Structure.naturality (to (forget-right-natural σ {T = T})) _ = morph-cong T refl
eq (isoˡ (forget-right-natural σ)) _ = refl
eq (isoʳ (forget-right-natural σ)) _ = refl

forget-right-cong : {Γ : Ctx ★} {T : Ty (just-left Γ)} {T' : Ty (just-left Γ)} →
                    T ≅ᵗʸ T' → forget-right T ≅ᵗʸ forget-right T'
func (from (forget-right-cong T=T')) = func (from T=T')
CwF-Structure.naturality (from (forget-right-cong T=T')) = CwF-Structure.naturality (from T=T')
func (to (forget-right-cong T=T')) = func (to T=T')
CwF-Structure.naturality (to (forget-right-cong T=T')) = CwF-Structure.naturality (to T=T')
eq (isoˡ (forget-right-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-right-cong T=T')) = eq (isoʳ T=T')

instance
  just-left-functor : IsCtxFunctor just-left
  IsCtxFunctor.ctx-map just-left-functor = just-left-subst
  IsCtxFunctor.ctx-map-id just-left-functor = just-left-subst-id
  IsCtxFunctor.ctx-map-⊚ just-left-functor = just-left-subst-⊚

  forget-right-unarynat : IsUnaryNatural forget-right
  IsUnaryNatural.natural-un forget-right-unarynat = forget-right-natural
  IsUnaryNatural.cong-un forget-right-unarynat = forget-right-cong

infixl 12 _⊛ʳ_
_⊛ʳ_ : {Γ : Ctx ★} {A B : Ty (just-left Γ)} →
       Tm Γ (forget-right (A ⇛ B)) → Tm Γ (forget-right A) → Tm Γ (forget-right B)
f ⊛ʳ a = forget-right-intro (forget-right-elim f $ forget-right-elim a)

just-right : Ctx ★ → Ctx ⋀
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

just-right-subst : {Δ : Ctx ★} {Γ : Ctx ★} → Δ ⇒ Γ → just-right Δ ⇒ just-right Γ
func (just-right-subst σ) {x = left}     = ⊥-elim
func (just-right-subst σ) {x = right}    = func σ
func (just-right-subst σ) {x = relation} = ⊥-elim
_⇒_.naturality (just-right-subst σ) {f = right-id} _ = refl

just-right-subst-id : {Γ : Ctx ★} → just-right-subst (id-subst Γ) ≅ˢ id-subst (just-right Γ)
eq just-right-subst-id {x = right} _ = refl

just-right-subst-⊚ : {Δ : Ctx ★} {Γ : Ctx ★} {Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                     just-right-subst (σ ⊚ τ) ≅ˢ just-right-subst σ ⊚ just-right-subst τ
eq (just-right-subst-⊚ σ τ) {x = right} _ = refl

forget-left : {Γ : Ctx ★} → Ty (just-right Γ) → Ty Γ
type (forget-left T) tt γ = T ⟨ right , γ ⟩
morph (forget-left {Γ = Γ} T) tt eγ = T ⟪ right-id , trans (sym (rel-id Γ _)) eγ ⟫_
morph-cong (forget-left T) refl {eγ = refl} {eγ' = refl} = refl
morph-id (forget-left T) t = trans (morph-cong T refl) (morph-id T t)
morph-comp (forget-left T) _ _ _ _ _ = sym (morph-cong-2-1 T refl)

module _ {Γ : Ctx ★} {T : Ty (just-right Γ)} where
  forget-left-intro : Tm (just-right Γ) T → Tm Γ (forget-left T)
  term (forget-left-intro t) _ γ = t ⟨ right , γ ⟩'
  Tm.naturality (forget-left-intro t) tt eγ = Tm.naturality t right-id _

  forget-left-elim : Tm Γ (forget-left T) → Tm (just-right Γ) T
  term (forget-left-elim t) right γ = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-left-elim t) right-id eγ = trans (morph-cong T refl) (Tm.naturality t tt (trans (rel-id Γ _) eγ))

forget-left-natural : {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ)
                      {T : Ty (just-right Γ)} →
                      (forget-left T) [ σ ] ≅ᵗʸ forget-left (T [ just-right-subst σ ])
func (from (forget-left-natural σ)) = id
CwF-Structure.naturality (from (forget-left-natural σ {T = T})) _ = morph-cong T refl
func (to (forget-left-natural σ)) = id
CwF-Structure.naturality (to (forget-left-natural σ {T = T})) _ = morph-cong T refl
eq (isoˡ (forget-left-natural σ)) _ = refl
eq (isoʳ (forget-left-natural σ)) _ = refl

forget-left-cong : {Γ : Ctx ★} {T : Ty (just-right Γ)} {T' : Ty (just-right Γ)} →
                   T ≅ᵗʸ T' → forget-left T ≅ᵗʸ forget-left T'
func (from (forget-left-cong T=T')) = func (from T=T')
CwF-Structure.naturality (from (forget-left-cong T=T')) = CwF-Structure.naturality (from T=T')
func (to (forget-left-cong T=T')) = func (to T=T')
CwF-Structure.naturality (to (forget-left-cong T=T')) = CwF-Structure.naturality (to T=T')
eq (isoˡ (forget-left-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-left-cong T=T')) = eq (isoʳ T=T')

instance
  just-right-functor : IsCtxFunctor just-right
  IsCtxFunctor.ctx-map just-right-functor = just-right-subst
  IsCtxFunctor.ctx-map-id just-right-functor = just-right-subst-id
  IsCtxFunctor.ctx-map-⊚ just-right-functor = just-right-subst-⊚

  forget-left-unarynat : IsUnaryNatural forget-left
  IsUnaryNatural.natural-un forget-left-unarynat = forget-left-natural
  IsUnaryNatural.cong-un forget-left-unarynat = forget-left-cong

infixl 12 _⊛ˡ_
_⊛ˡ_ : {Γ : Ctx ★} {A B : Ty (just-right Γ)} →
       Tm Γ (forget-left (A ⇛ B)) → Tm Γ (forget-left A) → Tm Γ (forget-left B)
f ⊛ˡ a = forget-left-intro (forget-left-elim f $ forget-left-elim a)

subtract-rep : Tm Γ (IntRep ⇛ IntRep ⇛ IntRep)
subtract-rep = subtract

subtract★-left : {Γ : Ctx ★} → Tm Γ (forget-right IntRep ⇛ forget-right IntRep ⇛ forget-right IntRep)
subtract★-left = lamι[ "i" ∈ forget-right IntRep ] lamι[ "j" ∈ forget-right IntRep ]
                 forget-right-intro subtract-rep ⊛ʳ varι "i" ⊛ʳ varι "j"

subtract★-right : {Γ : Ctx ★} → Tm Γ (forget-left IntRep ⇛ forget-left IntRep ⇛ forget-left IntRep)
subtract★-right = lamι[ "i" ∈ forget-left IntRep ] lamι[ "j" ∈ forget-left IntRep ]
                  forget-left-intro subtract-rep ⊛ˡ varι "i" ⊛ˡ varι "j"

open import Translation

instance
  forget-right-rel : {A B : Set} {R : REL A B 0ℓ} → Translatable (forget-right (FromRel A B R))
  Translatable.translated-type (forget-right-rel {A = A}) = A
  Translatable.translate-term forget-right-rel t = t ⟨ tt , tt ⟩'
  Translatable.translate-back forget-right-rel a = MkTm (λ _ _ → a) (λ _ _ → refl)
  Translatable.translate-cong forget-right-rel t=s = eq t=s tt

  forget-left-rel : {A B : Set} {R : REL A B 0ℓ} → Translatable (forget-left (FromRel A B R))
  Translatable.translated-type (forget-left-rel {B = B}) = B
  Translatable.translate-term forget-left-rel t = t ⟨ tt , tt ⟩'
  Translatable.translate-back forget-left-rel b = MkTm (λ _ _ → b) (λ _ _ → refl)
  Translatable.translate-cong forget-left-rel t=s = eq t=s tt
{-
subtract-left-agda : DiffInt → DiffInt → DiffInt
subtract-left-agda = translate-term subtract★-left

subtract-right-agda : SignNat → SignNat → SignNat
subtract-right-agda = translate-term subtract★-right

translate-result : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) subtract-left-agda subtract-right-agda
translate-result {d1}{s1} r1 {d2}{s2} r2 = proj₂ ((subtract-rep {Γ = ◇} €⟨ relation , tt ⟩ [ [ d1 , s1 ] , r1 ]) $⟨ relation-id , refl ⟩ [ [ d2 , s2 ] , r2 ])
-}
