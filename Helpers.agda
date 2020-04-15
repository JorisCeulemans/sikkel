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

uip : ∀ {a} {A : Set a} → UIP A
uip refl refl = refl

{-
-- Currently implemented by pattern matching on both e1 and e2. Can also be implemented
-- with option --without-K enabled since A → Lift ℓ ⊤ has decidable equality and is
-- therefore an hset (Hedberg's theorem).
to-⊤-hset : {A : Set ℓ'} {f g : A → Lift ℓ ⊤} (e1 e2 : f ≡ g) → e1 ≡ e2
to-⊤-hset refl refl = refl
-}

subst-const : ∀ {a b} {A : Set a} {B : Set b}
              {x x' : A} (e : x ≡ x') (y : B) →
              subst (λ _ → B) e y ≡ y
subst-const refl y = refl

subst-application' : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                     (B₁ : A₁ → Set b₁) {B₂ : A₂ → Set b₂} {f : A₁ → A₂} {x₁ x₂ : A₁}
                     {y : B₁ x₁} (g : (x : A₁) → B₁ x → B₂ (f x)) (eq : x₁ ≡ x₂) →
                     subst B₂ (cong f eq) (g x₁ y) ≡ g x₂ (subst B₁ eq y)
subst-application' B₁ g refl = refl

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

cong₄-d : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : (x : A) → B x → Set d} {E : Set e}
          (f : (x : A) (y : B x) → C x y → D x y → E)
          {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'} {w : D x y} {w' : D x' y'}
          (ex : x ≡ x') (ey : subst B ex y ≡ y') (ez : subst₂ C ex ey z ≡ z') (ew : subst₂ D ex ey w ≡ w') →
          f x y z w ≡ f x' y' z' w'
cong₄-d f refl refl refl refl = refl

cong-sym : ∀ {a b} {A : Set a} {B : Set b}
           (f : A → B)
           {a a' : A} (e : a ≡ a') →
           cong f (sym e) ≡ sym (cong f e)
cong-sym f refl = refl
{-
test : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : A → B → C → Set d}
       (f : (x : A) (y : B) (z : C) → D x y z)
       {x x' : A} {y : B} {z : C}
       (e : x ≡ x') →
       subst (λ u → (v : B) (w : C) → D u v w) e (f x) y z ≡ subst (λ u → D u y z) e (f x y z)
test f refl = refl
-}
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
