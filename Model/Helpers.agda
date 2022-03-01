module Model.Helpers where

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Level
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    ℓ ℓ' : Level

-- Should not be used except in Model.Type.Function and Model.CwF-Structure.Term.
postulate
  funext : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'
  funextI : ∀ {ℓ ℓ'} → ExtensionalityImplicit ℓ ℓ'

-- Shouldn't be used globally anymore, for the moment only in Model.Type.Function and Model.CwF-Structure.Term.
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
