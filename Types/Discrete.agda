--------------------------------------------------
-- Discrete types
--
-- Every Agda type can be turned into a type in any context.
-- This lets us define the types of booleans, natural numbers, ...
--------------------------------------------------

open import Categories

module Types.Discrete {C : Category} where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Nat hiding (_⊔_)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import Types.Functions
open import Reflection.Naturality

open Category C

private
  variable
    Γ Δ : Ctx C ℓ
    T : Ty Γ ℓ


--------------------------------------------------
-- General description of discrete types

Discr : (A : Set ℓ) → Ty Γ ℓ
type (Discr A) _ _ = A
morph (Discr A) _ _ = id
morph-cong (Discr A) _ = refl
morph-id (Discr A) _ = refl
morph-comp (Discr A) _ _ _ _ _ = refl

discr : {A : Set ℓ} → A → Tm Γ (Discr A)
term (discr a) _ _ = a
naturality (discr a) _ _ = refl

discr-func : {A : Set ℓ} {B : Set ℓ'} → (A → B) → Tm Γ (Discr A ⇛ Discr B)
term (discr-func f) _ _ $⟨ _ , _ ⟩ a = f a
naturality (term (discr-func f) _ _) _ _ _ = refl
naturality (discr-func f) _ _ = to-pshfun-eq λ _ _ _ → refl

{-
-- The following works if C = ω. In general, it will work if C has a
-- terminal or initial object. These results are however never used,
-- and therefore not yet generalized.
undiscr : {A : Set 0ℓ} → Tm ◇ (Discr A) → A
undiscr t = t ⟨ {!!} , lift tt ⟩'

undiscr-discr : {A : Set 0ℓ} (a : A) → undiscr (discr a) ≡ a
undiscr-discr a = refl

discr-undiscr : {A : Set 0ℓ} (t : Tm ◇ (Discr A)) → discr (undiscr t) ≅ᵗᵐ t
eq (discr-undiscr t) _ = sym (naturality t z≤n refl)
-}

Discr-natural : (A : Set ℓ) (σ : Δ ⇒ Γ) → Discr A [ σ ] ≅ᵗʸ Discr A
func (from (Discr-natural A σ)) = id
naturality (from (Discr-natural A σ)) _ = refl
func (to (Discr-natural A σ)) = id
naturality (to (Discr-natural A σ)) _ = refl
eq (isoˡ (Discr-natural A σ)) _ = refl
eq (isoʳ (Discr-natural A σ)) _ = refl

discr-natural : {A : Set ℓ} (a : A) (σ : Δ ⇒ Γ) → (discr a) [ σ ]' ≅ᵗᵐ ι[ Discr-natural A σ ] (discr a)
eq (discr-natural a σ) _ = refl


--------------------------------------------------
-- The unit type

Unit' : Ty Γ 0ℓ
Unit' = Discr ⊤

tt' : Tm Γ Unit'
tt' = discr tt

!unit : T ↣ Unit'
func !unit _ = tt
naturality !unit _ = refl

unit-terminal : (η : T ↣ Unit') → η ≅ⁿ !unit
eq (unit-terminal η) _ = refl

unit-elim : (T : Ty Γ ℓ) → Tm Γ T → Tm Γ (Unit' ⇛ T)
term (unit-elim T t) _ _ $⟨ _ , _ ⟩ _ = t ⟨ _ , _ ⟩'
naturality (term (unit-elim T t) _ _) _ eγ _ = sym (naturality t _ eγ)
naturality (unit-elim T t) f eγ = to-pshfun-eq λ _ _ _ → refl

β-unit' : {T : Ty Γ ℓ} (t : Tm Γ T) → app (unit-elim T t) tt' ≅ᵗᵐ t
eq (β-unit' t) _ = refl

η-unit' : (t : Tm Γ Unit') → t ≅ᵗᵐ tt'
eq (η-unit' t) _ = refl


--------------------------------------------------
-- Booleans

Bool' : Ty Γ 0ℓ
Bool' = Discr Bool

true' : Tm Γ Bool'
true' = discr true

false' : Tm Γ Bool'
false' = discr false

if'_then'_else'_ : Tm Γ Bool' → Tm Γ T → Tm Γ T → Tm Γ T
term (if' c then' t else' f) = λ x γ → if c ⟨ x , γ ⟩' then t ⟨ x , γ ⟩' else f ⟨ x , γ ⟩'
naturality (if'_then'_else'_ c t f) {x} {y} φ {γ} {γ'} eγ with c ⟨ x , γ' ⟩' | c ⟨ y , γ ⟩' | naturality c φ eγ
naturality (if'_then'_else'_ c t f) {x} {y} φ {γ} {γ'} eγ | false | .false | refl = naturality f φ eγ
naturality (if'_then'_else'_ c t f) {x} {y} φ {γ} {γ'} eγ | true  | .true  | refl = naturality t φ eγ

β-bool'-true : (t t' : Tm Γ T) →
               if' true' then' t else' t' ≅ᵗᵐ t
eq (β-bool'-true t t') _ = refl

β-bool'-false : (t t' : Tm Γ T) →
                if' false' then' t else' t' ≅ᵗᵐ t'
eq (β-bool'-false t t') _ = refl

η-bool' : (t : Tm Γ Bool') → t ≅ᵗᵐ if' t then' true' else' false'
eq (η-bool' t) γ with t ⟨ _ , γ ⟩'
eq (η-bool' t) γ | false = refl
eq (η-bool' t) γ | true  = refl

_||_ : Tm Γ Bool' → Tm Γ Bool' → Tm Γ Bool'
term (t || s) x γ = t ⟨ x , γ ⟩' ∨ s ⟨ x , γ ⟩'
naturality (t || s) f eγ = cong₂ _∨_ (naturality t f eγ) (naturality s f eγ)

_&&_ : Tm Γ Bool' → Tm Γ Bool' → Tm Γ Bool'
term (t && s) x γ = t ⟨ x , γ ⟩' ∧ s ⟨ x , γ ⟩'
naturality (t && s) f eγ = cong₂ _∧_ (naturality t f eγ) (naturality s f eγ)


--------------------------------------------------
-- Natural numbers

Nat' : Ty Γ 0ℓ
Nat' = Discr ℕ

zero' : Tm Γ Nat'
zero' = discr zero

suc' : Tm Γ Nat' → Tm Γ Nat'
term (suc' t) x γ = suc (t ⟨ x , γ ⟩')
naturality (suc' t) f γ = cong suc (naturality t f γ)

nat-elim : (T : Ty Γ ℓ) → Tm Γ T → Tm Γ (T ⇛ T) → Tm Γ (Nat' ⇛ T)
nat-elim {Γ = Γ} T t f = MkTm tm nat
  where
    open ≡-Reasoning
    tm : (x : Ob) (γ : Γ ⟨ x ⟩) → (Nat' ⇛ T) ⟨ x , γ ⟩
    tm x γ $⟨ ρ , eγ ⟩ zero = t ⟨ _ , _ ⟩'
    tm x γ $⟨ ρ , eγ ⟩ suc n = f €⟨ _ , _ ⟩ (tm x γ $⟨ ρ , eγ ⟩ n)
    naturality (tm z γ) eq-zy eq-yx zero = sym (naturality t _ eq-yx)
    naturality (tm z γ) eq-zy eq-yx (suc n) =
      begin
        f €⟨ _ , _ ⟩ (tm z γ $⟨ _ , _ ⟩ n)
      ≡⟨ cong (f €⟨ _ , _ ⟩_) (naturality (tm z γ) eq-zy eq-yx n) ⟩
        f €⟨ _ , _ ⟩ (T ⟪ _ , eq-yx ⟫ tm z γ $⟨ _ , eq-zy ⟩ n)
      ≡˘⟨ €-natural f _ eq-yx _ ⟩
        T ⟪ _ , eq-yx ⟫ (f €⟨ _ , _ ⟩ (tm z γ $⟨ _ , eq-zy ⟩ n)) ∎

    helper : {y z : Ob} {ρ-yz : Hom y z} {γy : Γ ⟨ y ⟩} {γz : Γ ⟨ z ⟩} (eq-zy : Γ ⟪ ρ-yz ⟫ γz ≡ γy) →
             {x : Ob} (ρ-xy : Hom x y) {γx : Γ ⟨ x ⟩} (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) (n : ℕ) →
             (Nat' ⇛ T ⟪ ρ-yz , eq-zy ⟫ tm z γz) $⟨ ρ-xy , eq-yx ⟩ n ≡ tm y γy $⟨ ρ-xy , eq-yx ⟩ n
    helper eq-zy ρ-xy eq-yx zero    = refl
    helper eq-zy ρ-xy eq-yx (suc n) = cong (f €⟨ _ , _ ⟩_) (helper eq-zy ρ-xy eq-yx n)

    nat : ∀ {y z} (ρ : Hom y z) {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γz ≡ γy) →
          Nat' ⇛ T ⟪ ρ , eγ ⟫ (tm z γz) ≡ tm y γy
    nat {y = y}{z = z} ρ-yz eq-zy = to-pshfun-eq (helper eq-zy)

β-nat-zero : {T : Ty Γ ℓ} (t : Tm Γ T) (f : Tm Γ (T ⇛ T)) →
             app (nat-elim T t f) zero' ≅ᵗᵐ t
eq (β-nat-zero t f) _ = refl

β-nat-suc : {T : Ty Γ ℓ} (t : Tm Γ T) (f : Tm Γ (T ⇛ T)) (k : Tm Γ Nat') →
            app (nat-elim T t f) (suc' k) ≅ᵗᵐ app f (app (nat-elim T t f) k)
eq (β-nat-suc t f k) _ = refl

η-nat : (k : Tm Γ Nat') → k ≅ᵗᵐ app (nat-elim Nat' zero' (discr-func suc)) k
eq (η-nat k) γ = go (k ⟨ _ , γ ⟩')
  where
    go : (n : ℕ) → n ≡ nat-elim Nat' zero' (discr-func suc) €⟨ _ , γ ⟩ n
    go zero    = refl
    go (suc n) = cong suc (go n)
