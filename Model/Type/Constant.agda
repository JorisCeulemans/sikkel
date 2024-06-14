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
    T S : Ty Γ


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

const-map : {A B : Set} → (A → B) → Tm Γ (Const A) → Tm Γ (Const B)
const-map f t ⟨ x , γ ⟩' = f (t ⟨ x , γ ⟩')
naturality (const-map f t) ρ eγ = cong f (naturality t ρ eγ)

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

const-map-natural : {A B : Set} (f : A → B) {σ : Δ ⇒ Γ} {t : Tm Γ (Const A)} →
                    (const-map f t) [ σ ]' ≅ᵗᵐ (ι[ Const-natural B σ ] const-map f (ι⁻¹[ Const-natural A σ ] (t [ σ ]')))
eq (const-map-natural f) _ = refl

const-map-cong : {A B : Set} (f : A → B) {t t' : Tm Γ (Const A)} → t ≅ᵗᵐ t' → const-map f t ≅ᵗᵐ const-map f t'
eq (const-map-cong f 𝒆) γ = cong f (eq 𝒆 γ)

const-closed : {A : Set} → IsClosedNatural {C} (Const A)
closed-natural (const-closed {A = A}) = Const-natural A
eq (from-eq (closed-id (const-closed {A = A}))) _ = refl
eq (from-eq (closed-⊚ (const-closed {A = A}) σ τ)) _ = refl
eq (from-eq (closed-subst-eq (const-closed {A = A}) ε)) _ = refl

const-cl-natural : {A : Set} {a : A} (σ : Δ ⇒ Γ) → (const a) [ const-closed ∣ σ ]cl ≅ᵗᵐ const a
const-cl-natural σ = transᵗᵐ (ι⁻¹-cong (const-natural _ σ)) ι-symˡ

const-map-cl-natural : {A B : Set} (f : A → B) {σ : Δ ⇒ Γ} {t : Tm Γ (Const A)} →
                       (const-map f t) [ const-closed ∣ σ ]cl ≅ᵗᵐ const-map f (t [ const-closed ∣ σ ]cl)
const-map-cl-natural f = transᵗᵐ (ι⁻¹-cong (const-map-natural f)) ι-symˡ


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

unit-β : {T : Ty Γ} (t : Tm Γ T) → app (unit-elim T t) tt' ≅ᵗᵐ t
eq (unit-β t) _ = refl

unit-η : (t : Tm Γ Unit') → t ≅ᵗᵐ tt'
eq (unit-η t) _ = refl


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

if'-cong : {b b' : Tm Γ Bool'} {t t' f f' : Tm Γ T} →
           b ≅ᵗᵐ b' → t ≅ᵗᵐ t' → f ≅ᵗᵐ f' →
           if' b then' t else' f ≅ᵗᵐ if' b' then' t' else' f'
eq (if'-cong {b = b} {b'} 𝒆b 𝒆t 𝒆f) γ with b ⟨ _ , γ ⟩' | b' ⟨ _ , γ ⟩' | eq 𝒆b γ
eq (if'-cong {b = b} {b'} 𝒆b 𝒆t 𝒆f) γ | false | .false | refl = eq 𝒆f γ
eq (if'-cong {b = b} {b'} 𝒆b 𝒆t 𝒆f) γ | true  | .true  | refl = eq 𝒆t γ

if'-natural : {σ : Γ ⇒ Δ} {b : Tm Δ Bool'} {t f : Tm Δ T} →
              (if' b then' t else' f) [ σ ]' ≅ᵗᵐ if' ι⁻¹[ Const-natural _ σ ] (b [ σ ]') then' (t [ σ ]') else' (f [ σ ]')
eq if'-natural γ = refl

if'-ι : {T=S : T ≅ᵗʸ S} {b : Tm Γ Bool'} {t f : Tm Γ S} →
        ι[ T=S ] (if' b then' t else' f) ≅ᵗᵐ if' b then' (ι[ T=S ] t) else' (ι[ T=S ] f)
eq (if'-ι {b = b}) γ with b ⟨ _ , γ ⟩'
eq (if'-ι {b = b}) γ | false = refl
eq (if'-ι {b = b}) γ | true  = refl

if'-cl-natural : {T : ClosedTy C} (clT : IsClosedNatural T) {σ : Γ ⇒ Δ} {b : Tm Δ Bool'} {t f : Tm Δ T} →
                 (if' b then' t else' f) [ clT ∣ σ ]cl ≅ᵗᵐ if' (b [ const-closed ∣ σ ]cl) then' (t [ clT ∣ σ ]cl) else' (f [ clT ∣ σ ]cl)
if'-cl-natural clT = transᵗᵐ (ι⁻¹-cong if'-natural) if'-ι

module _ (t t' : Tm Γ T) where
  if-β-true : if' true' then' t else' t' ≅ᵗᵐ t
  eq if-β-true _ = refl

  if-β-false : if' false' then' t else' t' ≅ᵗᵐ t'
  eq if-β-false _ = refl

bool-η : (t : Tm Γ Bool') → t ≅ᵗᵐ if' t then' true' else' false'
eq (bool-η t) γ with t ⟨ _ , γ ⟩'
eq (bool-η t) γ | false = refl
eq (bool-η t) γ | true  = refl

bool-ind : (T : Ty (Γ ,, Bool')) →
           Tm Γ (T [ true'  /cl⟨ const-closed ⟩ ]) →
           Tm Γ (T [ false' /cl⟨ const-closed ⟩ ]) →
           Tm (Γ ,, Bool') T
bool-ind T t f ⟨ x , [ γ , false ] ⟩' = f ⟨ x , γ ⟩'
bool-ind T t f ⟨ x , [ γ , true  ] ⟩' = t ⟨ x , γ ⟩'
naturality (bool-ind T t f) {γy = [ γy , false ]} ρ refl = naturality f ρ refl
naturality (bool-ind T t f) {γy = [ γy , true  ]} ρ refl = naturality t ρ refl

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

suc' : Tm Γ Nat' → Tm Γ Nat'
suc' = const-map suc

suc'-cong : {m n : Tm Γ Nat'} → m ≅ᵗᵐ n → suc' m ≅ᵗᵐ suc' n
suc'-cong = const-map-cong suc

suc'-const : {n : ℕ} {Γ : Ctx C} → suc' {Γ} (const n) ≅ᵗᵐ const (suc n)
eq suc'-const γ = refl

suc'-cl-natural : (σ : Γ ⇒ Δ) {n : Tm Δ Nat'} → (suc' n) [ const-closed ∣ σ ]cl ≅ᵗᵐ suc' (n [ const-closed ∣ σ ]cl)
suc'-cl-natural σ = transᵗᵐ (ι-cong (const-map-natural suc)) ι-symˡ

suc-func : Tm Γ (Nat' ⇛ Nat')
suc-func = const-func suc

prim-nat-rec : (T : Ty Γ) → Tm Γ T → Tm (Γ ,, T) (T [ π ]) → ℕ →  Tm Γ T
prim-nat-rec T z s zero    ⟨ x , γ ⟩' = z ⟨ x , γ ⟩'
prim-nat-rec T z s (suc n) ⟨ x , γ ⟩' = s ⟨ x , [ γ , prim-nat-rec T z s n ⟨ x , γ ⟩' ] ⟩'
naturality (prim-nat-rec T z s zero)    ρ refl = naturality z ρ refl
naturality (prim-nat-rec T z s (suc n)) ρ refl =
  trans (ty-cong T refl) (naturality s ρ (cong [ _ ,_] (naturality (prim-nat-rec T z s n) ρ refl)))

prim-nat-rec' : (T : Ty Γ) → Tm Γ T → Tm (Γ ,, T) (T [ π ]) → Tm Γ Nat' →  Tm Γ T
prim-nat-rec' T z s n ⟨ x , γ ⟩' = prim-nat-rec T z s (n ⟨ x , γ ⟩') ⟨ x , γ ⟩'
naturality (prim-nat-rec' {Γ = Γ} T z s n) {γy = γy} ρ refl with n ⟨ _ , γy ⟩' | n ⟨ _ , Γ ⟪ ρ ⟫ γy ⟩' | naturality n {γy = γy} ρ refl
naturality (prim-nat-rec' {Γ = Γ} T z s n) {γy = γy} ρ refl | m | .m | refl = naturality (prim-nat-rec T z s m) ρ refl

nat-rec : (T : Ty Γ) → Tm Γ T → Tm Γ (T ⇛ T) → Tm Γ Nat' →  Tm Γ T
nat-rec T z s n = prim-nat-rec' T z (ap s) n

prim-nat-rec-cong : {z z' : Tm Γ T} {s s' : Tm (Γ ,, T) (T [ π ])} →
                    z ≅ᵗᵐ z' → s ≅ᵗᵐ s' →
                    (n n' : ℕ) → n ≡ n' →
                    prim-nat-rec T z s n ≅ᵗᵐ prim-nat-rec T z' s' n'
eq (prim-nat-rec-cong           𝒆z 𝒆s zero    .zero    refl) γ = eq 𝒆z γ
eq (prim-nat-rec-cong {s' = s'} 𝒆z 𝒆s (suc n) .(suc n) refl) γ =
  trans (eq 𝒆s _) (cong (λ x → s' ⟨ _ , [ γ , x ] ⟩') (eq (prim-nat-rec-cong 𝒆z 𝒆s n n refl) γ))

nat-rec-cong : {z z' : Tm Γ T} {s s' : Tm Γ (T ⇛ T)} {n n' : Tm Γ Nat'} →
               z ≅ᵗᵐ z' → s ≅ᵗᵐ s' → n ≅ᵗᵐ n' →
               nat-rec T z s n ≅ᵗᵐ nat-rec T z' s' n'
eq (nat-rec-cong 𝒆z 𝒆s 𝒆n) γ = eq (prim-nat-rec-cong 𝒆z (ap-cong 𝒆s) _ _ (eq 𝒆n γ)) γ

prim-nat-rec-natural : {σ : Γ ⇒ Δ} {z : Tm Δ T} {s : Tm (Δ ,, T) (T [ π ])} (n : ℕ) →
                       (prim-nat-rec T z s n) [ σ ]' ≅ᵗᵐ prim-nat-rec (T [ σ ]) (z [ σ ]') (ι⁻¹[ ty-subst-cong-subst-2-2 T (⊹-π-comm σ) ] (s [ σ ⊹ ]')) n
eq (prim-nat-rec-natural                         zero)    γ = refl
eq (prim-nat-rec-natural {Δ = Δ} {T = T} {s = s} (suc n)) γ =
  sym (trans (ty-cong T refl) (naturality s hom-id (to-Σ-ty-eq T (ctx-id Δ) (trans (ty-cong-2-1 T hom-idʳ) (trans (ty-id T) (sym (eq (prim-nat-rec-natural n) γ)))))))

nat-rec-natural : {σ : Γ ⇒ Δ} {z : Tm Δ T} {s : Tm Δ (T ⇛ T)} {n : Tm Δ Nat'} →
                  (nat-rec T z s n) [ σ ]' ≅ᵗᵐ nat-rec (T [ σ ]) (z [ σ ]') (ι⁻¹[ ⇛-natural σ ] (s [ σ ]')) (ι⁻¹[ Const-natural _ σ ] (n [ σ ]'))
eq (nat-rec-natural {σ = σ} {n = n}) γ = trans (eq (prim-nat-rec-natural {σ = σ} (n ⟨ _ , func σ γ ⟩')) γ)
                                               (eq (prim-nat-rec-cong reflᵗᵐ tm-proof (n ⟨ _ , func σ γ ⟩') _ refl ) γ)
  where
    tm-proof = transᵗᵐ (ι⁻¹-cong (ap-natural σ _)) ι-symˡ

prim-nat-rec-ι : {T T' : Ty Γ} {T=T' : T ≅ᵗʸ T'} {z : Tm Γ T'} {s : Tm (Γ ,, T') (T' [ π ])} (n : ℕ) →
                 ι[ T=T' ] (prim-nat-rec T' z s n)
                   ≅ᵗᵐ
                 prim-nat-rec T (ι[ T=T' ] z)
                                 (ι⁻¹[ ty-subst-cong-subst-2-1 T (ctx-ext-subst-β₁ _ _) ]
                                       ((ι[ ty-subst-cong-ty π T=T' ] s) [ to-ext-subst _ π (ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ) ]'))
                                 n
eq (prim-nat-rec-ι zero)                                  γ = refl
eq (prim-nat-rec-ι {T = T} {T=T' = T=T'} {s = s} (suc n)) γ =
  trans (cong (λ x → func (to T=T') (s ⟨ _ , [ γ , x ] ⟩')) (trans (sym (eq (isoʳ T=T') _)) (cong (func (from T=T')) (eq (prim-nat-rec-ι n) γ))))
        (sym (strong-ty-id T))

nat-rec-ι : {T T' : Ty Γ} {T=T' : T ≅ᵗʸ T'} {z : Tm Γ T'} {s : Tm Γ (T' ⇛ T')} {n : Tm Γ Nat'} →
            ι[ T=T' ] (nat-rec T' z s n) ≅ᵗᵐ nat-rec T (ι[ T=T' ] z) (ι[ ⇛-cong T=T' T=T' ] s) n
eq (nat-rec-ι {T = T} {n = n}) γ = trans (eq (prim-nat-rec-ι (n ⟨ _ , γ ⟩')) γ) (eq (prim-nat-rec-cong reflᵗᵐ tm-proof _ (n ⟨ _ , γ ⟩') refl) γ)
  where
    tm-proof : _ ≅ᵗᵐ _
    eq tm-proof γ = strong-ty-id T

nat-rec-cl-natural : {T : ClosedTy C} (clT : IsClosedNatural T)
                     {σ : Γ ⇒ Δ} {z : Tm Δ T} {s : Tm Δ (T ⇛ T)} {n : Tm Δ Nat'} →
                     (nat-rec T z s n) [ clT ∣ σ ]cl ≅ᵗᵐ nat-rec T (z [ clT ∣ σ ]cl) (s [ fun-closed clT clT ∣ σ ]cl) (n [ const-closed ∣ σ ]cl)
nat-rec-cl-natural clT =
  transᵗᵐ (ι⁻¹-cong nat-rec-natural) (transᵗᵐ nat-rec-ι (nat-rec-cong reflᵗᵐ (transᵗᵐ (ι-congᵉ ⇛-cong-sym) (symᵗᵐ ι⁻¹-trans)) reflᵗᵐ))

module _ {T : Ty Γ} (z : Tm Γ T) (s : Tm Γ (T ⇛ T)) where
  nat-rec-β-zero : nat-rec T z s zero' ≅ᵗᵐ z
  eq nat-rec-β-zero _ = refl

  nat-rec-β-suc : (k : Tm Γ Nat') →
              nat-rec T z s (suc' k) ≅ᵗᵐ app s (nat-rec T z s k)
  eq (nat-rec-β-suc k) _ = refl

nat-η : (k : Tm Γ Nat') → k ≅ᵗᵐ nat-rec Nat' zero' suc-func k
eq (nat-η k) γ = go (k ⟨ _ , γ ⟩')
  where
    go : (n : ℕ) → n ≡ nat-rec Nat' zero' suc-func (const n) ⟨ _ , γ ⟩'
    go zero    = refl
    go (suc n) = cong suc (go n)

-- The following function could be defined inside Sikkel by using nat-rec.
-- However, with the following definition the extraction mechanism will produce Agda programs
-- that make use of Agda's `_+_` instead of a custom Sikkel definition, which leads to better performance.
nat-sum : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = const-func₂ _+_

-- The (dependent) induction principle for natural numbers.
nat-ind : (T : Ty (Γ ,, Nat')) →
          Tm Γ (T [ zero' /cl⟨ const-closed ⟩ ]) →
          Tm (Γ ,, Nat' ,, T) (T [ (π ,cl⟨ const-closed ⟩ suc' (ξcl const-closed)) ⊚ π ]) →
          Tm (Γ ,, Nat') T
nat-ind T z s ⟨ x , [ γ , zero  ] ⟩' = z ⟨ x , γ ⟩'
nat-ind T z s ⟨ x , [ γ , suc n ] ⟩' = s ⟨ x , [ [ γ , n ] , nat-ind T z s ⟨ x , [ γ , n ] ⟩' ] ⟩'
naturality (nat-ind T z s) {γy = [ _ , zero  ]} ρ refl = naturality z ρ refl
naturality (nat-ind T z s) {γy = [ _ , suc n ]} ρ refl =
  trans (ty-cong T refl) (naturality s ρ (cong [ _ ,_] (naturality (nat-ind T z s) {γy = [ _ , n ]} ρ refl)))
