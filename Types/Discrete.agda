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
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (setoid to ≡-setoid)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import Types.Functions

open Category C

private
  variable
    Γ Δ : Ctx C ℓ
    T : Ty Γ ℓ


--------------------------------------------------
-- General description of discrete types

Discr : (A : Set ℓ) → Ty Γ ℓ
type (Discr A) _ _ = ≡-setoid A
morph (Discr A) _ _ = id
morph-cong (Discr A) _ _ = id
morph-hom-cong (Discr A) _ = refl
morph-id (Discr A) _ = refl
morph-comp (Discr A) _ _ _ _ _ = refl

discr : {A : Set ℓ} → A → Tm Γ (Discr A)
term (discr a) _ _ = a
naturality (discr a) _ _ = refl

discr-func : {A : Set ℓ} {B : Set ℓ'} → (A → B) → Tm Γ (Discr A ⇛ Discr B)
term (discr-func f) _ _ $⟨ _ , _ ⟩ a = f a
$-cong (term (discr-func f) _ _) _ _ = cong f
$-hom-cong (term (discr-func f) _ _) _ = refl
naturality (term (discr-func f) _ _) _ _ _ = refl
naturality (discr-func f) _ _ _ _ _ = refl

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
func-cong (from (Discr-natural A σ)) = id
naturality (from (Discr-natural A σ)) _ = refl
func (to (Discr-natural A σ)) = id
func-cong (to (Discr-natural A σ)) = id
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
func-cong !unit _ = refl
naturality !unit _ = refl

unit-terminal : (η : T ↣ Unit') → η ≅ⁿ !unit
eq (unit-terminal η) _ = refl

unit-elim : (T : Ty Γ ℓ) → Tm Γ T → Tm Γ (Unit' ⇛ T)
term (unit-elim T t) _ _ $⟨ _ , _ ⟩ _ = t ⟨ _ , _ ⟩'
$-cong (term (unit-elim T t) _ _) _ _ _ = ty≈-refl T
$-hom-cong (term (unit-elim T t) _ _) _ = ty≈-refl T
naturality (term (unit-elim T t) _ _) _ eγ _ = ty≈-sym T (naturality t _ eγ)
naturality (unit-elim T t) _ _ _ _ _ = ty≈-refl T

β-unit' : {T : Ty Γ ℓ} (t : Tm Γ T) → app (unit-elim T t) tt' ≅ᵗᵐ t
eq (β-unit' {T = T} t) _ = ty≈-refl T

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

module _ (t t' : Tm Γ T) where
  β-bool'-true : if' true' then' t else' t' ≅ᵗᵐ t
  eq β-bool'-true _ = ty≈-refl T

  β-bool'-false : if' false' then' t else' t' ≅ᵗᵐ t'
  eq β-bool'-false _ = ty≈-refl T

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
    tm : (x : Ob) (γ : Γ ⟨ x ⟩) → (Nat' ⇛ T) ⟨ x , γ ⟩
    tm x γ $⟨ ρ , eγ ⟩ zero = t ⟨ _ , _ ⟩'
    tm x γ $⟨ ρ , eγ ⟩ suc n = f €⟨ _ , _ ⟩ (tm x γ $⟨ ρ , eγ ⟩ n)
    $-cong (tm x γ) _ _ refl = ty≈-refl T
    $-hom-cong (tm x γ) e-hom {t = zero } = ty≈-refl T
    $-hom-cong (tm x γ) e-hom {t = suc n} = $-cong (f ⟨ _ , _ ⟩') hom-id (rel-id Γ _) ($-hom-cong (tm x γ) e-hom {t = n})
    naturality (tm z γ) eq-zy eq-yx zero = ty≈-sym T (naturality t _ eq-yx)
    naturality (tm z γ) eq-zy eq-yx (suc n) =
      begin
        f €⟨ _ , _ ⟩ (tm z γ $⟨ _ , _ ⟩ n)
      ≈⟨ €-congʳ f (naturality (tm z γ) eq-zy eq-yx n) ⟩
        f €⟨ _ , _ ⟩ (T ⟪ _ , eq-yx ⟫ tm z γ $⟨ _ , eq-zy ⟩ n)
      ≈˘⟨ €-natural f _ eq-yx _ ⟩
        T ⟪ _ , eq-yx ⟫ (f €⟨ _ , _ ⟩ (tm z γ $⟨ _ , eq-zy ⟩ n)) ∎
      where
        open SetoidReasoning (type T _ _)

    helper : {y z : Ob} {ρ-yz : Hom y z} {γy : Γ ⟨ y ⟩} {γz : Γ ⟨ z ⟩} (eq-zy : Γ ⟪ ρ-yz ⟫ γz ≈[ Γ ]≈ γy) →
             {x : Ob} (ρ-xy : Hom x y) {γx : Γ ⟨ x ⟩} (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≈[ Γ ]≈ γx) (n : ℕ) →
             (Nat' ⇛ T ⟪ ρ-yz , eq-zy ⟫ tm z γz) $⟨ ρ-xy , eq-yx ⟩ n ≈⟦ T ⟧≈ tm y γy $⟨ ρ-xy , eq-yx ⟩ n
    helper eq-zy ρ-xy eq-yx zero    = ty≈-refl T
    helper eq-zy ρ-xy eq-yx (suc n) = €-congʳ f (helper eq-zy ρ-xy eq-yx n)

    nat : ∀ {y z} (ρ : Hom y z) {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γz ≈[ Γ ]≈ γy) →
          (Nat' ⇛ T) ⟪ ρ , eγ ⟫ (tm z γz) ≈⟦ Nat' ⇛ T ⟧≈ tm y γy
    nat {y = y}{z = z} ρ-yz = helper

module _ {T : Ty Γ ℓ} (t : Tm Γ T) (f : Tm Γ (T ⇛ T)) where
  β-nat-zero : app (nat-elim T t f) zero' ≅ᵗᵐ t
  eq β-nat-zero _ = ty≈-refl T

  β-nat-suc : (k : Tm Γ Nat') →
              app (nat-elim T t f) (suc' k) ≅ᵗᵐ app f (app (nat-elim T t f) k)
  eq (β-nat-suc k) _ = ty≈-refl T

η-nat : (k : Tm Γ Nat') → k ≅ᵗᵐ app (nat-elim Nat' zero' (discr-func suc)) k
eq (η-nat k) γ = go (k ⟨ _ , γ ⟩')
  where
    go : (n : ℕ) → n ≡ nat-elim Nat' zero' (discr-func suc) €⟨ _ , γ ⟩ n
    go zero    = refl
    go (suc n) = cong suc (go n)
