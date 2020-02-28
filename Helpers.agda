module Helpers where

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs
open import Data.Nat hiding (_⊔_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

variable
  ℓ ℓ' : Level
  k l m n : ℕ

postulate
  funext : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'
  funextI : ∀ {ℓ ℓ'} → ExtensionalityImplicit ℓ ℓ'
  funextI-irr : {A : Set ℓ} {B : .A → Set ℓ'} {f g : .{x : A} → B x} →
                (∀ {x} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

uip : ∀ {a} {A : Set a} → UIP A
uip refl refl = refl

-- Currently implemented by pattern matching on both e1 and e2. Can also be implemented
-- with option --without-K enabled since A → Lift ℓ ⊤ has decidable equality and is
-- therefore an hset (Hedberg's theorem).
to-⊤-hset : {A : Set ℓ'} {f g : A → Lift ℓ ⊤} (e1 e2 : f ≡ g) → e1 ≡ e2
to-⊤-hset refl refl = refl

weak-subst-application : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
                         (f : (x : A) → B x → C x)
                         {x x' : A} {y : B x}
                         (ex : x ≡ x') →
                         subst C ex (f x y) ≡ f x' (subst B ex y)
weak-subst-application f refl = refl

function-subst : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
                 {x x' : A} (ex : x ≡ x') {y : B x'}
                 (f : B x → C x) →
                 (subst (λ z → B z → C z) ex f) y ≡ subst C ex (f (subst B (sym ex) y))
function-subst refl f = refl

subst₂ : ∀ {a b c} {A : Set a} {B : A → Set b} (C : (x : A) → B x → Set c)
         {x x' : A} {y : B x} {y' : B x'}
         (ex : x ≡ x') (ey : subst B ex y ≡ y') →
         C x y → C x' y'
subst₂ C refl refl c = c

cong-d : {A : Set ℓ} {B : A → Set ℓ'}
         (f : (x : A) → B x)
         {a a' : A} (e : a ≡ a') →
         subst B e (f a) ≡ f a'
cong-d f refl = refl

cong₂-d : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
          (f : (x : A) → B x → C)
          {x x' : A} {y : B x} {y' : B x'}
          (ex : x ≡ x') (ey : subst B ex y ≡ y') →
          f x y ≡ f x' y'
cong₂-d f refl refl = refl

cong₃-d : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : Set d}
          (f : (x : A) (y : B x) → C x y → D)
          {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'}
          (ex : x ≡ x') (ey : subst B ex y ≡ y') (ez : subst₂ C ex ey z ≡ z') →
          f x y z ≡ f x' y' z'
cong₃-d f refl refl refl = refl

test : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : A → B → C → Set d}
       (f : (x : A) (y : B) (z : C) → D x y z)
       {x x' : A} {y : B} {z : C}
       (e : x ≡ x') →
       subst (λ u → (v : B) (w : C) → D u v w) e (f x) y z ≡ subst (λ u → D u y z) e (f x y z)
test f refl = refl

subst-cong-app : ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c}
                 {f g : A → B} (e : f ≡ g)
                 {x : A} (z : C (f x)) →
                 subst C (cong-app e x) z ≡ subst (λ - → C (- x)) e z
subst-cong-app refl z = refl

to-Σ-eq : {A : Set ℓ} {B : A → Set ℓ'}
          {a a' : A} {b : B a} {b' : B a'}
          (e1 : a ≡ a') (e2 : subst B e1 b ≡ b') →
          [ a , b ] ≡ [ a' , b' ]
to-Σ-eq e1 e2 = cong₂-d [_,_] e1 e2
