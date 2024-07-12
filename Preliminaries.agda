-- Definition of some operations which are not in the standard library

module Preliminaries where

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Data.Vec as Vec using (Vec; _∷_; [])
import Data.Vec.Properties as Vec
open import Function
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Syntax

private
  variable
    a ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C : Set a


--------------------------------------------------
-- Some results about propositional equality

-- Should not be used except in Types.Functions and CwF-Structure.Terms.
postulate
  funext : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'
  funextI : ∀ {ℓ ℓ'} → ExtensionalityImplicit ℓ ℓ'

-- Shouldn't be used globally anymore, for the moment only in Types.Functions and CwF-Structure.Terms.
uip : ∀ {a} {A : Set a} → UIP A
uip refl refl = refl

cong₂-d : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
          (f : (x : A) → B x → C)
          {x x' : A} {y : B x} {y' : B x'}
          (ex : x ≡ x') (ey : subst B ex y ≡ y') →
          f x y ≡ f x' y'
cong₂-d f refl refl = refl

to-Σ-eq : {A : Set ℓ} {B : A → Set ℓ'}
          {a a' : A} {b : B a} {b' : B a'}
          (e1 : a ≡ a') (e2 : subst B e1 b ≡ b') →
          [ a , b ] ≡ [ a' , b' ]
to-Σ-eq e1 e2 = cong₂-d [_,_] e1 e2

from-Σ-eq1 : {A : Set ℓ} {B : A → Set ℓ'}
             {p q : Σ A B} →
             p ≡ q → proj₁ p ≡ proj₁ q
from-Σ-eq1 e = cong proj₁ e

from-Σ-eq2 : {A : Set ℓ} {B : A → Set ℓ'}
             {p q : Σ A B} →
             (e : p ≡ q) →
             subst B (from-Σ-eq1 e) (proj₂ p) ≡ proj₂ q
from-Σ-eq2 refl = refl

from-to-Σ-eq1 : ∀ {a b} {A : Set a} {B : A → Set b}
                {x x' : A} {y : B x} {y' : B x'}
                {ex : x ≡ x'} (ey : subst B ex y ≡ y') →
                from-Σ-eq1 (to-Σ-eq ex ey) ≡ ex
from-to-Σ-eq1 {ex = refl} refl = refl


--------------------------------------------------
-- Extension of syntax for reasoning combinators to include the ones for ≅

module ≅-syntax
  {R : REL A B ℓ₂}
  (S : REL B C ℓ₁)
  (T : REL A C ℓ₃)
  (step : Trans R S T)
  {U : REL B A ℓ₄}
  (sym : Sym U R)
  where

  infixr 2 step-≅-⟩ step-≅-⟨ step-≅-∣
  step-≅-⟩ = forward S T step
  step-≅-⟨ = backward S T step sym

  step-≅-∣ : ∀ x {y} → R x y → R x y
  step-≅-∣ x xRy = xRy

  syntax step-≅-⟩ x yRz x≅y = x ≅⟨ x≅y ⟩ yRz
  syntax step-≅-⟨ x yRz y≅x = x ≅⟨ y≅x ⟨ yRz
  syntax step-≅-∣ x xRy     = x ≅⟨⟩ xRy


--------------------------------------------------
-- Some basic operations and proofs regarding vectors

first-≤ : ∀ {m n} {A : Set ℓ} → m ≤ n → Vec A n → Vec A m
first-≤ z≤n       as       = []
first-≤ (s≤s m≤n) (a ∷ as) = a ∷ first-≤ m≤n as

first-≤-refl : ∀ {n} {A : Set ℓ} {as : Vec A n} → first-≤ (≤-refl) as ≡ as
first-≤-refl {as = []}     = refl
first-≤-refl {as = a ∷ as} = cong (a ∷_) first-≤-refl

first-≤-trans : ∀ {k m n} {A : Set ℓ} {k≤m : k ≤ m} {m≤n : m ≤ n} {as : Vec A n} →
                first-≤ (≤-trans k≤m m≤n) as ≡ first-≤ k≤m (first-≤ m≤n as)
first-≤-trans {k≤m = z≤n}                                   = refl
first-≤-trans {k≤m = s≤s k≤m} {m≤n = s≤s m≤n} {as = a ∷ as} = cong (a ∷_) first-≤-trans

map-first-≤ : ∀ {m n} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {m≤n : m ≤ n} {as : Vec A n} →
              Vec.map f (first-≤ m≤n as) ≡ first-≤ m≤n (Vec.map f as)
map-first-≤         {m≤n = z≤n}              = refl
map-first-≤ {f = f} {m≤n = s≤s m≤n} {a ∷ as} = cong (f a ∷_) map-first-≤

first-≤-head : ∀ {m n} {A : Set ℓ} {m≤n : m ≤ n} (as : Vec A (suc n)) →
               Vec.head (first-≤ (s≤s m≤n) as) ≡ Vec.head as
first-≤-head (a ∷ as) = refl

map-head : ∀ {n} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (as : Vec A (suc n)) →
           Vec.head (Vec.map f as) ≡ f (Vec.head as)
map-head (a ∷ as) = refl

first-≤-tail : ∀ {m n} {A : Set ℓ} {m≤n : m ≤ n} (as : Vec A (suc n)) →
               Vec.tail (first-≤ (s≤s m≤n) as) ≡ first-≤ m≤n (Vec.tail as)
first-≤-tail (a ∷ as) = refl

map-tail : ∀ {n} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (as : Vec A (suc n)) →
           Vec.tail (Vec.map f as) ≡ Vec.map f (Vec.tail as)
map-tail (a ∷ as) = refl

map-map-cong : ∀ {n ℓa ℓb ℓc ℓd} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {D : Set ℓd}
               {f : A → B} {g : B → D} {f' : A → C} {g' : C → D} (e : g ∘ f ≗ g' ∘ f')
               {as : Vec A n} →
               Vec.map g (Vec.map f as) ≡ Vec.map g' (Vec.map f' as)
map-map-cong {f = f}{g}{f'}{g'} e {as} =
  begin
    Vec.map g (Vec.map f as)
  ≡⟨ Vec.map-∘ g f as ⟨
    Vec.map (g ∘ f) as
  ≡⟨ Vec.map-cong e as ⟩
    Vec.map (g' ∘ f') as
  ≡⟨ Vec.map-∘ g' f' as ⟩
    Vec.map g' (Vec.map f' as) ∎
  where open ≡-Reasoning

map-inverse : ∀ {n} {A : Set ℓ} {B : Set ℓ'}
              {f : A → B} {g : B → A} (e : g ∘ f ≗ id)
              {as : Vec A n} →
              Vec.map g (Vec.map f as) ≡ as
map-inverse {f = f}{g} e {as} =
  begin
    Vec.map g (Vec.map f as)
  ≡⟨ Vec.map-∘ g f as ⟨
    Vec.map (g ∘ f) as
  ≡⟨ Vec.map-cong e as ⟩
    Vec.map id as
  ≡⟨ Vec.map-id as ⟩
    as ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Standard streams in Agda (note that the standard library uses sized
-- types which we want to avoid)

record Stream {ℓ} (A : Set ℓ) : Set ℓ where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

take : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → Stream A → Vec A n
take zero    s = []
take (suc n) s = head s ∷ take n (tail s)

take-first : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} (m≤n : m ≤ n) (s : Stream A) →
             first-≤ m≤n (take n s) ≡ take m s
take-first z≤n       s = refl
take-first (s≤s m≤n) s = cong (head s ∷_) (take-first m≤n (tail s))

record Bisimilar {ℓ} {A : Set ℓ} (s1 s2 : Stream A) : Set ℓ where
  coinductive
  field
    head : head s1 ≡ head s2
    tail : Bisimilar (tail s1) (tail s2)
open Bisimilar public


-- We show that streams are isomorphic to growing sequences of vectors
-- (satisfying the necessary naturality condition), under the
-- assumption of stream extensionality.
record GrowingVec {ℓ} (A : Set ℓ) : Set ℓ where
  constructor growing-vec
  field
    vec : (n : ℕ) → Vec A (suc n)
    vec-natural : {m n : ℕ} (m≤n : m ≤ n) → first-≤ (s≤s m≤n) (vec n) ≡ vec m
open GrowingVec

to-growing-vec-eq : {gv1 gv2 : GrowingVec A} →
                    ((n : ℕ) → vec gv1 n ≡ vec gv2 n) →
                    gv1 ≡ gv2
to-growing-vec-eq vecs-eq =
  cong₂-d growing-vec (funext vecs-eq) (funextI (funextI (funext (λ _ → uip _ _))))

growing-vec-tail-suc : GrowingVec A → GrowingVec A
vec (growing-vec-tail-suc vecs) n = Vec.tail (vec vecs (suc n))
vec-natural (growing-vec-tail-suc vecs) m≤n =
  trans (sym (first-≤-tail (vec vecs (suc _)))) (cong Vec.tail (vec-natural vecs (s≤s m≤n)))

growing-vec-to-stream : GrowingVec A → Stream A
head (growing-vec-to-stream vecs) = Vec.head (vec vecs 0)
tail (growing-vec-to-stream vecs) = growing-vec-to-stream (growing-vec-tail-suc vecs)

stream-to-growing-vec : Stream A → GrowingVec A
vec (stream-to-growing-vec s) n = take (suc n) s
vec-natural (stream-to-growing-vec s) m≤n = take-first (s≤s m≤n) s

growing-vec-diagonal : GrowingVec A → (n : ℕ) → Vec A (suc n)
growing-vec-diagonal vecs zero    = Vec.head (vec vecs 0) ∷ []
growing-vec-diagonal vecs (suc n) = Vec.head (vec vecs 0) ∷ growing-vec-diagonal (growing-vec-tail-suc vecs) n

growing-vec-diagonal-vertical : (vecs : GrowingVec A) (n : ℕ) →
                                growing-vec-diagonal vecs n ≡ vec vecs n
growing-vec-diagonal-vertical vecs zero    = vec-1-η (vec vecs zero)
  where
    vec-1-η : (v : Vec A 1) → Vec.head v ∷ [] ≡ v
    vec-1-η (a ∷ []) = refl
growing-vec-diagonal-vertical vecs (suc n) =
  trans (cong₂ _∷_ (trans (cong Vec.head (sym (vec-natural vecs z≤n))) (first-≤-head (vec vecs (suc n))))
                   (growing-vec-diagonal-vertical (growing-vec-tail-suc vecs) n))
        (vec-η _)
  where
    vec-η : {n : ℕ} (v : Vec A (suc n)) → Vec.head v ∷ Vec.tail v ≡ v
    vec-η (a ∷ t) = refl

take-to-stream-diagonal : (vecs : GrowingVec A) (n : ℕ) →
                          take (suc n) (growing-vec-to-stream vecs) ≡ growing-vec-diagonal vecs n
take-to-stream-diagonal vecs zero    = refl
take-to-stream-diagonal vecs (suc n) = cong (_ ∷_) (take-to-stream-diagonal (growing-vec-tail-suc vecs) n)

gv-stream-gv : (vecs : GrowingVec A) → stream-to-growing-vec (growing-vec-to-stream vecs) ≡ vecs
gv-stream-gv vecs = to-growing-vec-eq (λ n → trans (take-to-stream-diagonal vecs n) (growing-vec-diagonal-vertical vecs n))


take-equal-bisimilar : {s1 s2 : Stream A} →
                       ((n : ℕ) → take n s1 ≡ take n s2) →
                       Bisimilar s1 s2
head (take-equal-bisimilar te) = cong Vec.head (te 1)
tail (take-equal-bisimilar {s1 = s1} {s2} te) = take-equal-bisimilar (λ n → cong Vec.tail (te (suc n)))

stream-to-growing-vec-tail : (s : Stream A) → growing-vec-tail-suc (stream-to-growing-vec s) ≡ stream-to-growing-vec (tail s)
stream-to-growing-vec-tail s = to-growing-vec-eq (λ _ → refl)

stream-gv-stream-take : (s : Stream A) (n : ℕ) →
                        take n (growing-vec-to-stream (stream-to-growing-vec s)) ≡ take n s
stream-gv-stream-take s zero    = refl
stream-gv-stream-take s (suc n) =
  cong (head s ∷_) (trans (cong (λ x → take n (growing-vec-to-stream x)) (stream-to-growing-vec-tail s)) (stream-gv-stream-take (tail s) n))

stream-gv-stream-bisimilar : (s : Stream A) →
                             Bisimilar (growing-vec-to-stream (stream-to-growing-vec s)) s
stream-gv-stream-bisimilar s = take-equal-bisimilar (stream-gv-stream-take s)


-- Stream extensionality should only be used in the isomorphism below,
-- nowhere else in the library. Only the extraction mechanism for
-- streams relies on this principle.
postulate
  streamext : ∀ {ℓ} {A : Set ℓ} {s1 s2 : Stream A} → Bisimilar s1 s2 → s1 ≡ s2


growvec-stream-iso : {A : Set ℓ} → GrowingVec A ↔ Stream A
growvec-stream-iso = mk↔ₛ′
  growing-vec-to-stream
  stream-to-growing-vec
  (λ s → streamext (stream-gv-stream-bisimilar s))
  gv-stream-gv
