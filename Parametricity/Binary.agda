--------------------------------------------------
-- An example of representation independence using
-- binary parametricity
--------------------------------------------------

module Parametricity.Binary where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Function using (id; _∘_)
open import Level using (0ℓ)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Types.Instances
open import Modalities
open import Reflection.Naturality.TypeOperations
open import Reflection.SubstitutionSequence
open import Reflection.Tactic.Lambda
open import Translation

private
  variable
    Γ : Ctx ⋀


--------------------------------------------------
-- Constructing an embedded type in base category ⋀
-- using two Agda types and a relation

PrimFromRel : (A B : Set) (R : REL A B 0ℓ) → Ty {C = ⋀} ◇
PrimFromRel A B R ⟨ left ,  _ ⟩ = A
PrimFromRel A B R ⟨ right , _ ⟩ = B
PrimFromRel A B R ⟨ relation , _ ⟩ = Σ[ p ∈ A × B ] uncurry R p
_⟪_,_⟫_ (PrimFromRel A B R) left-id  _ = id
_⟪_,_⟫_ (PrimFromRel A B R) right-id _ = id
_⟪_,_⟫_ (PrimFromRel A B R) relation-id _ = id
_⟪_,_⟫_ (PrimFromRel A B R) left-rel  _ = proj₁ ∘ proj₁
_⟪_,_⟫_ (PrimFromRel A B R) right-rel _ = proj₂ ∘ proj₁
ty-cong (PrimFromRel A B R) refl {eγ = refl}{eγ' = refl} = refl
ty-id (PrimFromRel A B R) {x = left}  = refl
ty-id (PrimFromRel A B R) {x = right} = refl
ty-id (PrimFromRel A B R) {x = relation} = refl
ty-comp (PrimFromRel A B R) {f = left-id}     {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromRel A B R) {f = right-id}    {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromRel A B R) {f = relation-id} {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromRel A B R) {f = left-rel}  {g = relation-id} = refl
ty-comp (PrimFromRel A B R) {f = right-rel} {g = relation-id} = refl

FromRel : (A B : Set) (R : REL A B 0ℓ) → ClosedType ⋀
FromRel A B R {Γ = Γ} = PrimFromRel A B R [ !◇ Γ ]

instance
  fromrel-natural : {A B : Set} {R : REL A B 0ℓ} → IsClosedNatural (FromRel A B R)
  natural-nul {{fromrel-natural}} σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) (PrimFromRel _ _ _) (◇-terminal _ _ _)

from-rel : {A B : Set} {R : REL A B 0ℓ} (a : A) (b : B) → R a b → Tm Γ (FromRel A B R)
from-rel a b r ⟨ left  , _ ⟩' = a
from-rel a b r ⟨ right , _ ⟩' = b
from-rel a b r ⟨ relation , _ ⟩' = [ [ a , b ] , r ]
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
from-rel1 f g h ⟨ left  , [ _ , a ] ⟩' = f a
from-rel1 f g h ⟨ right , [ _ , b ] ⟩' = g b
from-rel1 f g h ⟨ relation , [ _ , [ [ a , b ] , r ] ] ⟩' = [ [ f a , g b ] , h r ]
Tm.naturality (from-rel1 f g h) left-id refl = refl
Tm.naturality (from-rel1 f g h) right-id refl = refl
Tm.naturality (from-rel1 f g h) relation-id refl = refl
Tm.naturality (from-rel1 f g h) left-rel refl = refl
Tm.naturality (from-rel1 f g h) right-rel refl = refl

from-rel2 : {A1 B1 : Set} {R1 : REL A1 B1 0ℓ}
            {A2 B2 : Set} {R2 : REL A2 B2 0ℓ}
            {A3 B3 : Set} {R3 : REL A3 B3 0ℓ}
            (f : A1 → A2 → A3) (g : B1 → B2 → B3) → (R1 ⟨→⟩ R2 ⟨→⟩ R3) f g →
            Tm (Γ ,, FromRel A1 B1 R1 ,, FromRel A2 B2 R2) (FromRel A3 B3 R3)
from-rel2 f g h ⟨ left  , [ [ _ , a1 ] , a2 ] ⟩' = f a1 a2
from-rel2 f g h ⟨ right , [ [ _ , b1 ] , b2 ] ⟩' = g b1 b2
from-rel2 f g h ⟨ relation , [ [ _ , [ [ a1 , b1 ] , r1 ] ] , [ [ a2 , b2 ] , r2 ] ] ⟩' = [ [ f a1 a2 , g b1 b2 ] , h r1 r2 ]
Tm.naturality (from-rel2 f g h) left-id  refl = refl
Tm.naturality (from-rel2 f g h) right-id refl = refl
Tm.naturality (from-rel2 f g h) relation-id refl = refl
Tm.naturality (from-rel2 f g h) left-rel  refl = refl
Tm.naturality (from-rel2 f g h) right-rel refl = refl


--------------------------------------------------
-- Example: types representing integers

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


--------------------------------------------------
-- Definition of 2 modalities from ⋀ to ★.

just-left : Ctx ★ → Ctx ⋀
just-left Γ ⟨ left  ⟩ = Γ ⟨ tt ⟩
just-left Γ ⟨ right ⟩ = ⊥
just-left Γ ⟨ relation ⟩ = ⊥
_⟪_⟫_ (just-left Γ) left-id = id
_⟪_⟫_ (just-left Γ) right-id = id
_⟪_⟫_ (just-left Γ) relation-id = id
_⟪_⟫_ (just-left Γ) left-rel = ⊥-elim
_⟪_⟫_ (just-left Γ) right-rel = id
ctx-id (just-left Γ) {x = left} = refl
ctx-comp (just-left Γ) {f = left-id} = refl
ctx-comp (just-left Γ) {f = right-id} = refl
ctx-comp (just-left Γ) {f = relation-id} = refl
ctx-comp (just-left Γ) {f = left-rel} {g = relation-id} = refl
ctx-comp (just-left Γ) {f = right-rel} {g = relation-id} = refl

just-left-subst : {Δ Γ : Ctx ★} → Δ ⇒ Γ → just-left Δ ⇒ just-left Γ
func (just-left-subst σ) {x = left}     = func σ
func (just-left-subst σ) {x = right}    = ⊥-elim
func (just-left-subst σ) {x = relation} = ⊥-elim
_⇒_.naturality (just-left-subst σ) {f = left-id} = refl

just-left-subst-cong : {Δ Γ : Ctx ★} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → just-left-subst σ ≅ˢ just-left-subst τ
eq (just-left-subst-cong σ=τ) {x = left} δ = eq σ=τ δ

just-left-subst-id : {Γ : Ctx ★} → just-left-subst (id-subst Γ) ≅ˢ id-subst (just-left Γ)
eq just-left-subst-id {x = left} _ = refl

just-left-subst-⊚ : {Δ Γ Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                    just-left-subst (σ ⊚ τ) ≅ˢ just-left-subst σ ⊚ just-left-subst τ
eq (just-left-subst-⊚ σ τ) {x = left} _ = refl

forget-right-ty : {Γ : Ctx ★} → Ty (just-left Γ) → Ty Γ
forget-right-ty T ⟨ tt , γ ⟩ = T ⟨ left , γ ⟩
forget-right-ty {Γ = Γ} T ⟪ tt , eγ ⟫ t = T ⟪ left-id , trans (sym (ctx-id Γ)) eγ ⟫ t
ty-cong (forget-right-ty T) refl {eγ = refl} {eγ' = refl} = refl
ty-id (forget-right-ty T) = strong-ty-id T
ty-comp (forget-right-ty T) = strong-ty-comp T

module _ {Γ : Ctx ★} {T : Ty (just-left Γ)} where
  forget-right-tm : Tm (just-left Γ) T → Tm Γ (forget-right-ty T)
  forget-right-tm t ⟨ _ , γ ⟩' = t ⟨ left , γ ⟩'
  Tm.naturality (forget-right-tm t) tt eγ = Tm.naturality t left-id _

  unforget-right-tm : Tm Γ (forget-right-ty T) → Tm (just-left Γ) T
  unforget-right-tm t ⟨ left , γ ⟩' = t ⟨ tt , γ ⟩'
  Tm.naturality (unforget-right-tm t) left-id eγ = trans (ty-cong T refl) (Tm.naturality t tt (trans (ctx-id Γ) eγ))

module _ {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) {T : Ty (just-left Γ)} where
  forget-right-ty-natural : (forget-right-ty T) [ σ ] ≅ᵗʸ forget-right-ty (T [ just-left-subst σ ])
  func (from forget-right-ty-natural) = id
  CwF-Structure.naturality (from forget-right-ty-natural) = ty-cong T refl
  func (to forget-right-ty-natural) = id
  CwF-Structure.naturality (to forget-right-ty-natural) = ty-cong T refl
  eq (isoˡ forget-right-ty-natural) _ = refl
  eq (isoʳ forget-right-ty-natural) _ = refl

  forget-right-tm-natural : (t : Tm (just-left Γ) T) →
                            forget-right-tm t [ σ ]' ≅ᵗᵐ ι[ forget-right-ty-natural ] forget-right-tm (t [ just-left-subst σ ]')
  eq (forget-right-tm-natural t) _ = refl

  unforget-right-tm-natural : (t : Tm Γ (forget-right-ty T)) →
                              unforget-right-tm t [ just-left-subst σ ]' ≅ᵗᵐ unforget-right-tm (ι⁻¹[ forget-right-ty-natural ] (t [ σ ]'))
  eq (unforget-right-tm-natural t) {x = left} _ = refl

forget-right-ty-cong : {Γ : Ctx ★} {T : Ty (just-left Γ)} {T' : Ty (just-left Γ)} →
                       T ≅ᵗʸ T' → forget-right-ty T ≅ᵗʸ forget-right-ty T'
func (from (forget-right-ty-cong T=T')) = func (from T=T')
CwF-Structure.naturality (from (forget-right-ty-cong T=T')) = CwF-Structure.naturality (from T=T')
func (to (forget-right-ty-cong T=T')) = func (to T=T')
CwF-Structure.naturality (to (forget-right-ty-cong T=T')) = CwF-Structure.naturality (to T=T')
eq (isoˡ (forget-right-ty-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-right-ty-cong T=T')) = eq (isoʳ T=T')

module _ {Γ : Ctx ★} {T : Ty (just-left Γ)} where
  forget-right-tm-cong : {t t' : Tm (just-left Γ) T} → t ≅ᵗᵐ t' → forget-right-tm t ≅ᵗᵐ forget-right-tm t'
  eq (forget-right-tm-cong t=t') γ = eq t=t' γ

  unforget-right-tm-cong : {t t' : Tm Γ (forget-right-ty T)} → t ≅ᵗᵐ t' → unforget-right-tm t ≅ᵗᵐ unforget-right-tm t'
  eq (unforget-right-tm-cong t=t') {x = left} γ = eq t=t' γ

  forget-right-β : (t : Tm (just-left Γ) T) → unforget-right-tm (forget-right-tm t) ≅ᵗᵐ t
  eq (forget-right-β t) {x = left} _ = refl

  forget-right-η : (t : Tm Γ (forget-right-ty T)) → forget-right-tm (unforget-right-tm t) ≅ᵗᵐ t
  eq (forget-right-η t) _ = refl

module _ {Γ : Ctx ★} {T S : Ty (just-left Γ)} (T=S : T ≅ᵗʸ S) where
  forget-right-tm-ι : (s : Tm (just-left Γ) S) → ι[ forget-right-ty-cong T=S ] forget-right-tm s ≅ᵗᵐ forget-right-tm (ι[ T=S ] s)
  eq (forget-right-tm-ι s) _ = refl

  unforget-right-tm-ι : (s : Tm Γ (forget-right-ty S)) → ι[ T=S ] unforget-right-tm s ≅ᵗᵐ unforget-right-tm (ι[ forget-right-ty-cong T=S ] s)
  eq (unforget-right-tm-ι s) {x = left} _ = refl

instance
  just-left-functor : IsCtxFunctor just-left
  ctx-map {{just-left-functor}} = just-left-subst
  ctx-map-cong {{just-left-functor}} = just-left-subst-cong
  ctx-map-id {{just-left-functor}} = just-left-subst-id
  ctx-map-⊚ {{just-left-functor}} = just-left-subst-⊚

  forget-right-unarynat : IsUnaryNatural forget-right-ty
  IsUnaryNatural.natural-un forget-right-unarynat = forget-right-ty-natural
  IsUnaryNatural.cong-un forget-right-unarynat = forget-right-ty-cong

forget-right : Modality ⋀ ★
forget-right = record
   { ctx-op = just-left
   ; mod = forget-right-ty
   ; mod-cong = forget-right-ty-cong
   ; mod-natural = forget-right-ty-natural
   ; mod-intro = forget-right-tm
   ; mod-intro-cong = forget-right-tm-cong
   ; mod-intro-natural = forget-right-tm-natural
   ; mod-intro-ι = forget-right-tm-ι
   ; mod-elim = unforget-right-tm
   ; mod-elim-cong = unforget-right-tm-cong
   ; mod-β = forget-right-β
   ; mod-η = forget-right-η
   }

just-right : Ctx ★ → Ctx ⋀
just-right Γ ⟨ left  ⟩ = ⊥
just-right Γ ⟨ right ⟩ = Γ ⟨ tt ⟩
just-right Γ ⟨ relation ⟩ = ⊥
_⟪_⟫_ (just-right Γ) left-id = id
_⟪_⟫_ (just-right Γ) right-id = id
_⟪_⟫_ (just-right Γ) relation-id = id
_⟪_⟫_ (just-right Γ) left-rel = id
_⟪_⟫_ (just-right Γ) right-rel = ⊥-elim
ctx-id (just-right Γ) {x = right} = refl
ctx-comp (just-right Γ) {f = left-id} = refl
ctx-comp (just-right Γ) {f = right-id} = refl
ctx-comp (just-right Γ) {f = relation-id} = refl
ctx-comp (just-right Γ) {f = left-rel} {g = relation-id} = refl
ctx-comp (just-right Γ) {f = right-rel} {g = relation-id} = refl

just-right-subst : {Δ Γ : Ctx ★} → Δ ⇒ Γ → just-right Δ ⇒ just-right Γ
func (just-right-subst σ) {x = left}     = ⊥-elim
func (just-right-subst σ) {x = right}    = func σ
func (just-right-subst σ) {x = relation} = ⊥-elim
_⇒_.naturality (just-right-subst σ) {f = right-id} = refl

just-right-subst-cong : {Δ Γ : Ctx ★} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → just-right-subst σ ≅ˢ just-right-subst τ
eq (just-right-subst-cong σ=τ) {x = right} δ = eq σ=τ δ

just-right-subst-id : {Γ : Ctx ★} → just-right-subst (id-subst Γ) ≅ˢ id-subst (just-right Γ)
eq just-right-subst-id {x = right} _ = refl

just-right-subst-⊚ : {Δ Γ Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                     just-right-subst (σ ⊚ τ) ≅ˢ just-right-subst σ ⊚ just-right-subst τ
eq (just-right-subst-⊚ σ τ) {x = right} _ = refl

forget-left-ty : {Γ : Ctx ★} → Ty (just-right Γ) → Ty Γ
forget-left-ty T ⟨ tt , γ ⟩ = T ⟨ right , γ ⟩
forget-left-ty {Γ = Γ} T ⟪ tt , eγ ⟫ t = T ⟪ right-id , trans (sym (ctx-id Γ)) eγ ⟫ t
ty-cong (forget-left-ty T) refl {eγ = refl} {eγ' = refl} = refl
ty-id (forget-left-ty T) = strong-ty-id T
ty-comp (forget-left-ty T) = strong-ty-comp T

module _ {Γ : Ctx ★} {T : Ty (just-right Γ)} where
  forget-left-tm : Tm (just-right Γ) T → Tm Γ (forget-left-ty T)
  forget-left-tm t ⟨ _ , γ ⟩' = t ⟨ right , γ ⟩'
  Tm.naturality (forget-left-tm t) tt eγ = Tm.naturality t right-id _

  unforget-left-tm : Tm Γ (forget-left-ty T) → Tm (just-right Γ) T
  unforget-left-tm t ⟨ right , γ ⟩' = t ⟨ tt , γ ⟩'
  Tm.naturality (unforget-left-tm t) right-id eγ = trans (ty-cong T refl) (Tm.naturality t tt (trans (ctx-id Γ) eγ))

module _ {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) {T : Ty (just-right Γ)} where
  forget-left-ty-natural : (forget-left-ty T) [ σ ] ≅ᵗʸ forget-left-ty (T [ just-right-subst σ ])
  func (from forget-left-ty-natural) = id
  CwF-Structure.naturality (from forget-left-ty-natural) = ty-cong T refl
  func (to forget-left-ty-natural) = id
  CwF-Structure.naturality (to forget-left-ty-natural) = ty-cong T refl
  eq (isoˡ forget-left-ty-natural) _ = refl
  eq (isoʳ forget-left-ty-natural) _ = refl

  forget-left-tm-natural : (t : Tm (just-right Γ) T) →
                           forget-left-tm t [ σ ]' ≅ᵗᵐ ι[ forget-left-ty-natural ] forget-left-tm (t [ just-right-subst σ ]')
  eq (forget-left-tm-natural t) _ = refl

  unforget-left-tm-natural : (t : Tm Γ (forget-left-ty T)) →
                             unforget-left-tm t [ just-right-subst σ ]' ≅ᵗᵐ unforget-left-tm (ι⁻¹[ forget-left-ty-natural ] (t [ σ ]'))
  eq (unforget-left-tm-natural t) {x = right} _ = refl

forget-left-ty-cong : {Γ : Ctx ★} {T : Ty (just-right Γ)} {T' : Ty (just-right Γ)} →
                      T ≅ᵗʸ T' → forget-left-ty T ≅ᵗʸ forget-left-ty T'
func (from (forget-left-ty-cong T=T')) = func (from T=T')
CwF-Structure.naturality (from (forget-left-ty-cong T=T')) = CwF-Structure.naturality (from T=T')
func (to (forget-left-ty-cong T=T')) = func (to T=T')
CwF-Structure.naturality (to (forget-left-ty-cong T=T')) = CwF-Structure.naturality (to T=T')
eq (isoˡ (forget-left-ty-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-left-ty-cong T=T')) = eq (isoʳ T=T')

module _ {Γ : Ctx ★} {T : Ty (just-right Γ)} where
  forget-left-tm-cong : {t t' : Tm (just-right Γ) T} → t ≅ᵗᵐ t' → forget-left-tm t ≅ᵗᵐ forget-left-tm t'
  eq (forget-left-tm-cong t=t') γ = eq t=t' γ

  unforget-left-tm-cong : {t t' : Tm Γ (forget-left-ty T)} → t ≅ᵗᵐ t' → unforget-left-tm t ≅ᵗᵐ unforget-left-tm t'
  eq (unforget-left-tm-cong t=t') {x = right} γ = eq t=t' γ

  forget-left-β : (t : Tm (just-right Γ) T) → unforget-left-tm (forget-left-tm t) ≅ᵗᵐ t
  eq (forget-left-β t) {x = right} _ = refl

  forget-left-η : (t : Tm Γ (forget-left-ty T)) → forget-left-tm (unforget-left-tm t) ≅ᵗᵐ t
  eq (forget-left-η t) _ = refl

module _ {Γ : Ctx ★} {T S : Ty (just-right Γ)} (T=S : T ≅ᵗʸ S) where
  forget-left-tm-ι : (s : Tm (just-right Γ) S) → ι[ forget-left-ty-cong T=S ] forget-left-tm s ≅ᵗᵐ forget-left-tm (ι[ T=S ] s)
  eq (forget-left-tm-ι s) _ = refl

  unforget-left-tm-ι : (s : Tm Γ (forget-left-ty S)) → ι[ T=S ] unforget-left-tm s ≅ᵗᵐ unforget-left-tm (ι[ forget-left-ty-cong T=S ] s)
  eq (unforget-left-tm-ι s) {x = right} _ = refl

instance
  just-right-functor : IsCtxFunctor just-right
  ctx-map {{just-right-functor}} = just-right-subst
  ctx-map-cong {{just-right-functor}} = just-right-subst-cong
  ctx-map-id {{just-right-functor}} = just-right-subst-id
  ctx-map-⊚ {{just-right-functor}} = just-right-subst-⊚

  forget-left-unarynat : IsUnaryNatural forget-left-ty
  IsUnaryNatural.natural-un forget-left-unarynat = forget-left-ty-natural
  IsUnaryNatural.cong-un forget-left-unarynat = forget-left-ty-cong

forget-left : Modality ⋀ ★
forget-left = record
   { ctx-op = just-right
   ; mod = forget-left-ty
   ; mod-cong = forget-left-ty-cong
   ; mod-natural = forget-left-ty-natural
   ; mod-intro = forget-left-tm
   ; mod-intro-cong = forget-left-tm-cong
   ; mod-intro-natural = forget-left-tm-natural
   ; mod-intro-ι = forget-left-tm-ι
   ; mod-elim = unforget-left-tm
   ; mod-elim-cong = unforget-left-tm-cong
   ; mod-β = forget-left-β
   ; mod-η = forget-left-η
   }


--------------------------------------------------
-- Continuing the example of integer representations.

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
