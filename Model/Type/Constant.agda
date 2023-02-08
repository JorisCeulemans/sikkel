--------------------------------------------------
-- Constant presheaves
--
-- Every Agda type can be turned into a presheaf type in any context.
-- This lets us define the types of booleans, natural numbers, ...
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Constant {C : BaseCategory} where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.Type.Function

open BaseCategory C

private
  variable
    Γ Δ : Ctx C
    T : Ty Γ


--------------------------------------------------
-- General description of constant presheaves

Const : (A : Set) → Ty Γ
Const A ⟨ _ , _ ⟩ = A
Const A ⟪ _ , _ ⟫ a = a
ty-cong (Const A) _ = refl
ty-id (Const A) = refl
ty-comp (Const A) = refl

const : {A : Set} → A → Tm Γ (Const A)
const a ⟨ _ , _ ⟩' = a
naturality (const a) _ _ = refl

const-func : {A B : Set} → (A → B) → Tm Γ (Const A ⇛ Const B)
(const-func f ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ a = f a
naturality (const-func f ⟨ _ , _ ⟩') = refl
naturality (const-func f) _ _ = to-pshfun-eq λ _ _ _ → refl

const-func₂ : {A B C : Set} → (A → B → C) → Tm Γ (Const A ⇛ Const B ⇛ Const C)
(const-func₂ f ⟨ _ , _ ⟩' $⟨ _ , _ ⟩ a) $⟨ _ , _ ⟩ b = f a b
naturality (const-func₂ f ⟨ _ , _ ⟩' $⟨ _ , _ ⟩ _) = refl
naturality (const-func₂ f ⟨ _ , _ ⟩') = to-pshfun-eq (λ _ _ _ → refl)
naturality (const-func₂ f) _ _ = to-pshfun-eq (λ _ _ _ → refl)

{-
-- The following works if C = ω. In general, it will work if C has a
-- terminal or initial object. These results are however never used,
-- and therefore not yet generalized.
unconst : {A : Set 0ℓ} → Tm ◇ (Const A) → A
unconst t = t ⟨ {!!} , lift tt ⟩'

unconst-const : {A : Set 0ℓ} (a : A) → unconst (const a) ≡ a
unconst-const a = refl

const-unconst : {A : Set 0ℓ} (t : Tm ◇ (Const A)) → const (unconst t) ≅ᵗᵐ t
eq (const-unconst t) _ = sym (naturality t z≤n refl)
-}

Const-natural : (A : Set) (σ : Δ ⇒ Γ) → Const A [ σ ] ≅ᵗʸ Const A
func (from (Const-natural A σ)) = id
naturality (from (Const-natural A σ)) = refl
func (to (Const-natural A σ)) = id
naturality (to (Const-natural A σ)) = refl
eq (isoˡ (Const-natural A σ)) _ = refl
eq (isoʳ (Const-natural A σ)) _ = refl

const-natural : {A : Set} (a : A) (σ : Δ ⇒ Γ) → (const a) [ σ ]' ≅ᵗᵐ ι[ Const-natural A σ ] (const a)
eq (const-natural a σ) _ = refl

const-closed : {A : Set} → IsClosedNatural {C} (Const A)
closed-natural (const-closed {A = A}) = Const-natural A
eq (from-eq (closed-id (const-closed {A = A}))) _ = refl
eq (from-eq (closed-⊚ (const-closed {A = A}) σ τ)) _ = refl
eq (from-eq (closed-subst-eq (const-closed {A = A}) ε)) _ = refl

const-cl-natural : {A : Set} {a : A} (σ : Δ ⇒ Γ) → (const a) [ const-closed ∣ σ ]cl ≅ᵗᵐ const a
const-cl-natural σ = transᵗᵐ (ι⁻¹-cong (const-natural _ σ)) ι-symˡ


--------------------------------------------------
-- The unit type

Unit' : Ty Γ
Unit' = Const ⊤

tt' : Tm Γ Unit'
tt' = const tt

!unit : T ↣ Unit'
func !unit _ = tt
naturality !unit = refl

unit-terminal : (η : T ↣ Unit') → η ≅ⁿ !unit
eq (unit-terminal η) _ = refl

unit-elim : (T : Ty Γ) → Tm Γ T → Tm Γ (Unit' ⇛ T)
(unit-elim T t ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ _ = t ⟨ _ , _ ⟩'
naturality (unit-elim T t ⟨ _ , _ ⟩') = sym (naturality t _ _)
naturality (unit-elim T t) _ _ = to-pshfun-eq λ _ _ _ → refl

β-unit : {T : Ty Γ} (t : Tm Γ T) → app (unit-elim T t) tt' ≅ᵗᵐ t
eq (β-unit t) _ = refl

η-unit : (t : Tm Γ Unit') → t ≅ᵗᵐ tt'
eq (η-unit t) _ = refl


--------------------------------------------------
-- The empty type

Empty' : Ty Γ
Empty' = Const ⊥

empty-elim : (T : Ty Γ) → Tm Γ (Empty' ⇛ T)
empty-elim T ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ ()
naturality (empty-elim T ⟨ x , γ ⟩') {t = ()}
naturality (empty-elim T) f eγ = to-pshfun-eq (λ _ _ ())


--------------------------------------------------
-- Booleans

Bool' : Ty Γ
Bool' = Const Bool

true' : Tm Γ Bool'
true' = const true

false' : Tm Γ Bool'
false' = const false

if'_then'_else'_ : Tm Γ Bool' → Tm Γ T → Tm Γ T → Tm Γ T
(if' c then' t else' f) ⟨ x , γ ⟩' = if c ⟨ x , γ ⟩' then t ⟨ x , γ ⟩' else f ⟨ x , γ ⟩'
naturality (if'_then'_else'_ c t f) {x} {y} {γ} {γ'} φ eγ with c ⟨ x , γ' ⟩' | c ⟨ y , γ ⟩' | naturality c φ eγ
naturality (if'_then'_else'_ c t f) {x} {y} {γ} {γ'} φ eγ | false | .false | refl = naturality f φ eγ
naturality (if'_then'_else'_ c t f) {x} {y} {γ} {γ'} φ eγ | true  | .true  | refl = naturality t φ eγ

module _ (t t' : Tm Γ T) where
  β-bool-true : if' true' then' t else' t' ≅ᵗᵐ t
  eq β-bool-true _ = refl

  β-bool-false : if' false' then' t else' t' ≅ᵗᵐ t'
  eq β-bool-false _ = refl

η-bool : (t : Tm Γ Bool') → t ≅ᵗᵐ if' t then' true' else' false'
eq (η-bool t) γ with t ⟨ _ , γ ⟩'
eq (η-bool t) γ | false = refl
eq (η-bool t) γ | true  = refl

_||_ : Tm Γ Bool' → Tm Γ Bool' → Tm Γ Bool'
t || s ⟨ x , γ ⟩' = t ⟨ x , γ ⟩' ∨ s ⟨ x , γ ⟩'
naturality (t || s) f eγ = cong₂ _∨_ (naturality t f eγ) (naturality s f eγ)

_&&_ : Tm Γ Bool' → Tm Γ Bool' → Tm Γ Bool'
t && s ⟨ x , γ ⟩' = t ⟨ x , γ ⟩' ∧ s ⟨ x , γ ⟩'
naturality (t && s) f eγ = cong₂ _∧_ (naturality t f eγ) (naturality s f eγ)


--------------------------------------------------
-- Natural numbers

Nat' : Ty Γ
Nat' = Const ℕ

zero' : Tm Γ Nat'
zero' = const zero

one' : Tm Γ Nat'
one' = const (suc zero)

suc' : Tm Γ (Nat' ⇛ Nat')
suc' = const-func suc

suc'-const : {n : ℕ} {Γ : Ctx C} → app {Γ = Γ} suc' (const n) ≅ᵗᵐ const (suc n)
eq suc'-const γ = refl

prim-nat-elim : (T : Ty Γ) → Tm Γ T → Tm (Γ ,, T) (T [ π ]) → Tm (Γ ,, Nat') (T [ π ])
prim-nat-elim T t f ⟨ x , [ γ , zero  ] ⟩' = t ⟨ x , γ ⟩'
prim-nat-elim T t f ⟨ x , [ γ , suc n ] ⟩' = f ⟨ x , [ γ , prim-nat-elim T t f ⟨ x , [ γ , n ] ⟩' ] ⟩'
naturality (prim-nat-elim T t f) {γy = [ _ , zero ]} {γx = [ _ , zero ]} ρ refl = naturality t ρ refl
naturality (prim-nat-elim T t f) {γy = [ _ , suc n ]} {γx = [ _ , suc n ]} ρ refl =
  trans (ty-cong T refl) (naturality f ρ (cong [ _ ,_] (naturality (prim-nat-elim T t f) {γy = [ _ , n ]} ρ refl)))

nat-elim : (T : Ty Γ) → Tm Γ T → Tm Γ (T ⇛ T) → Tm Γ (Nat' ⇛ T)
nat-elim T t f = lam Nat' (prim-nat-elim T t (ap f))

module _ {T : Ty Γ} (t : Tm Γ T) (f : Tm Γ (T ⇛ T)) where
  β-nat-zero : app (nat-elim T t f) zero' ≅ᵗᵐ t
  eq β-nat-zero _ = refl

  β-nat-suc : (k : Tm Γ Nat') →
              app (nat-elim T t f) (suc' $ k) ≅ᵗᵐ app f (app (nat-elim T t f) k)
  eq (β-nat-suc k) _ = refl

η-nat : (k : Tm Γ Nat') → k ≅ᵗᵐ app (nat-elim Nat' zero' suc') k
eq (η-nat k) γ = go (k ⟨ _ , γ ⟩')
  where
    go : (n : ℕ) → n ≡ nat-elim Nat' zero' suc' €⟨ _ , γ ⟩ n
    go zero    = refl
    go (suc n) = cong suc (go n)

-- The following function could be defined inside Sikkel by using nat-elim.
-- However, with the following definition the extraction mechanism will produce Agda programs
-- that make use of Agda's `_+_` instead of a custom Sikkel definition, which leads to better performance.
nat-sum : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = const-func₂ _+_
