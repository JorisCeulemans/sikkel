--------------------------------------------------
-- Definition of semantic guarded streams in base category ω
--------------------------------------------------

module Applications.GuardedRecursion.Model.Streams.Guarded where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Vec hiding ([_]; _⊛_)
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)
open import Level renaming (zero to lzero; suc to lsuc)

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.DRA
open import Applications.GuardedRecursion.Model.Modalities

private
  variable
    ℓ ℓ' : Level
    Γ Δ : Ctx ω


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
              map f (first-≤ m≤n as) ≡ first-≤ m≤n (map f as)
map-first-≤         {m≤n = z≤n}              = refl
map-first-≤ {f = f} {m≤n = s≤s m≤n} {a ∷ as} = cong (f a ∷_) map-first-≤

first-≤-head : ∀ {m n} {A : Set ℓ} {m≤n : m ≤ n} (as : Vec A (suc n)) →
               head (first-≤ (s≤s m≤n) as) ≡ head as
first-≤-head (a ∷ as) = refl

map-head : ∀ {n} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (as : Vec A (suc n)) →
           head (map f as) ≡ f (head as)
map-head (a ∷ as) = refl

first-≤-tail : ∀ {m n} {A : Set ℓ} {m≤n : m ≤ n} (as : Vec A (suc n)) →
               tail (first-≤ (s≤s m≤n) as) ≡ first-≤ m≤n (tail as)
first-≤-tail (a ∷ as) = refl

map-tail : ∀ {n} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (as : Vec A (suc n)) →
           tail (map f as) ≡ map f (tail as)
map-tail (a ∷ as) = refl

map-map-cong : ∀ {n ℓa ℓb ℓc ℓd} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {D : Set ℓd}
               {f : A → B} {g : B → D} {f' : A → C} {g' : C → D} (e : g ∘ f ≗ g' ∘ f')
               {as : Vec A n} →
               map g (map f as) ≡ map g' (map f' as)
map-map-cong {f = f}{g}{f'}{g'} e {as} =
  begin
    map g (map f as)
  ≡⟨ map-∘ g f as ⟨
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map (g' ∘ f') as
  ≡⟨ map-∘ g' f' as ⟩
    map g' (map f' as) ∎
  where open ≡-Reasoning

map-inverse : ∀ {n} {A : Set ℓ} {B : Set ℓ'}
              {f : A → B} {g : B → A} (e : g ∘ f ≗ id)
              {as : Vec A n} →
              map g (map f as) ≡ as
map-inverse {f = f}{g} e {as} =
  begin
    map g (map f as)
  ≡⟨ map-∘ g f as ⟨
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map id as
  ≡⟨ map-id as ⟩
    as ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Definition of guarded streams.

GStream : Ty (now Γ) → Ty Γ
GStream {Γ = Γ} A ⟨ n , γ ⟩ = Vec (constantly-ty A ⟨ n , γ ⟩) (suc n)
GStream A ⟪ m≤n , eγ ⟫ v = map (constantly-ty A ⟪ m≤n , eγ ⟫_) (first-≤ (s≤s m≤n) v)
ty-cong (GStream A) refl = map-cong (λ _ → ty-cong A refl) _
ty-id (GStream A) {t = v} =
  begin
    map (constantly-ty A ⟪ ≤-refl , _ ⟫_) (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-cong (λ _ → ty-id (constantly-ty A)) (first-≤ (s≤s ≤-refl) v) ⟩
    map id (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-id (first-≤ (s≤s ≤-refl) v) ⟩
    first-≤ (s≤s ≤-refl) v
  ≡⟨ first-≤-refl ⟩
    v ∎
  where open ≡-Reasoning
ty-comp (GStream A) {f = k≤m} {g = m≤n} {eγ-zy = eγ-nm} {eγ-yx = eγ-mk} {t = v} =
  begin
    map (constantly-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s (≤-trans k≤m m≤n)) v)
  ≡⟨ cong (map (constantly-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_)) first-≤-trans ⟩
    map (constantly-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-cong (λ _ → ty-comp (constantly-ty A)) _ ⟩
    map (constantly-ty A ⟪ k≤m , eγ-mk ⟫_ ∘ constantly-ty A ⟪ m≤n , eγ-nm ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-∘ (constantly-ty A ⟪ k≤m , eγ-mk ⟫_) (constantly-ty A ⟪ m≤n , eγ-nm ⟫_) _ ⟩
    map (constantly-ty A ⟪ k≤m , eγ-mk ⟫_) (map (constantly-ty A ⟪ m≤n , eγ-nm ⟫_)
      (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v)))
  ≡⟨ cong (map (constantly-ty A ⟪ k≤m , eγ-mk ⟫_)) map-first-≤ ⟩
    map (constantly-ty A ⟪ k≤m , eγ-mk ⟫_) (first-≤ (s≤s k≤m)
      (map (constantly-ty A ⟪ m≤n , eγ-nm ⟫_) (first-≤ (s≤s m≤n) v))) ∎
  where open ≡-Reasoning

module _ {A : Ty (now Γ)} where
  g-head : Tm Γ (GStream A) → Tm Γ (constantly-ty A)
  g-head s ⟨ n , γ ⟩' = head (s ⟨ n , γ ⟩')
  naturality (g-head s) {x = m} {n} {γn} {γm} m≤n eγ =
    begin
      A ⟪ tt , _ ⟫ head (s ⟨ n , γn ⟩')
    ≡⟨ cong (A ⟪ tt , _ ⟫_) (first-≤-head (s ⟨ n , γn ⟩')) ⟨
      A ⟪ tt , _ ⟫ head (first-≤ (s≤s m≤n) (s ⟨ n , γn ⟩'))
    ≡⟨ map-head (first-≤ (s≤s m≤n) (s ⟨ n , γn ⟩')) ⟨
      head (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s m≤n) (s ⟨ n , γn ⟩')))
    ≡⟨ cong head (naturality s m≤n eγ) ⟩
      head (s ⟨ m , γm ⟩') ∎
    where open ≡-Reasoning

  g-tail : Tm Γ (GStream A) → Tm Γ (▻' (GStream A))
  g-tail s ⟨ zero ,  γ ⟩' = _
  g-tail s ⟨ suc n , γ ⟩' = map (ty-ctx-subst A (ctx-comp Γ)) (tail (s ⟨ suc n , γ ⟩'))
  naturality (g-tail s) z≤n eγ = refl
  naturality (g-tail s) {x = suc m} {y = suc n} {γy = γn} {γx = γm} (s≤s m≤n) eγ =
    let α = _
        β = _
    in
    begin
      map (A ⟪ tt , α ⟫_) (first-≤ (s≤s m≤n) (map (A ⟪ tt , β ⟫_) (tail (s ⟨ suc n , γn ⟩'))))
    ≡⟨ trans (map-tail (first-≤ (s≤s (s≤s m≤n)) (map (A ⟪ tt , β ⟫_) (s ⟨ suc n , γn ⟩')))) (
       trans (cong (map (A ⟪ tt , α ⟫_)) (first-≤-tail (map (A ⟪ tt , β ⟫_) (s ⟨ suc n , γn ⟩')))) (
       (cong (map (A ⟪ tt , α ⟫_)) (cong (first-≤ (s≤s m≤n)) (map-tail (s ⟨ suc n , γn ⟩')))))) ⟨
      tail (map (A ⟪ tt , α ⟫_) (first-≤ (s≤s (s≤s m≤n)) (map (A ⟪ tt , β ⟫_) (s ⟨ suc n , γn ⟩'))))
    ≡⟨ cong tail (cong (map (A ⟪ tt , α ⟫_)) (map-first-≤ {m≤n = s≤s (s≤s m≤n)} {as = s ⟨ suc n , γn ⟩'})) ⟨
      tail (map (A ⟪ tt , α ⟫_) (map (A ⟪ tt , β ⟫_) (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γn ⟩'))))
    ≡⟨ cong tail (map-map-cong (λ _ → ty-cong-2-2 A refl) {as = first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γn ⟩')}) ⟩
      tail (map (ty-ctx-subst A (ctx-comp Γ)) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γn ⟩'))))
    ≡⟨ cong tail (cong (map (ty-ctx-subst A (ctx-comp Γ))) (naturality s (s≤s m≤n) eγ)) ⟩
      tail (map (ty-ctx-subst A (ctx-comp Γ)) (s ⟨ suc m , γm ⟩'))
    ≡⟨ map-tail (s ⟨ suc m , γm ⟩') ⟩
      map (ty-ctx-subst A (ctx-comp Γ)) (tail (s ⟨ suc m , γm ⟩')) ∎
    where open ≡-Reasoning

  g-cons : Tm Γ (constantly-ty A) → Tm Γ (▻' (GStream A)) → Tm Γ (GStream A)
  g-cons a s ⟨ zero  , γ ⟩' = a ⟨ zero , γ ⟩' ∷ []
  g-cons a s ⟨ suc n , γ ⟩' = a ⟨ suc n , γ ⟩' ∷ map (ty-ctx-subst A (sym (ctx-comp Γ))) (s ⟨ suc n , γ ⟩')
  naturality (g-cons a s) {y = zero}  z≤n eγ = cong (_∷ []) (naturality a z≤n eγ)
  naturality (g-cons a s) {y = suc _} z≤n eγ = cong (_∷ []) (naturality a z≤n eγ)
  naturality (g-cons a s) {x = suc m} {y = suc n} {γy = γn} {γx = γm} (s≤s m≤n) eγ =
    cong₂ _∷_ (naturality a (s≤s m≤n) eγ) (
      begin
        map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s m≤n) (map (A ⟪ tt , _ ⟫_) (s ⟨ suc n , γn ⟩')))
      ≡⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟨
        map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s m≤n) (s ⟨ suc n , γn ⟩')))
      ≡⟨ map-map-cong (λ _ → ty-cong-2-2 A refl) ⟩
        map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s m≤n) (s ⟨ suc n , γn ⟩')))
      ≡⟨ cong (map (A ⟪ tt , _ ⟫_)) (naturality s (s≤s m≤n) eγ) ⟩
        map (A ⟪ tt , _ ⟫_) (s ⟨ suc m , γm ⟩') ∎)
    where open ≡-Reasoning

  gstream-natural : (σ : Δ ⇒ Γ) → (GStream A) [ σ ] ≅ᵗʸ GStream (A [ now-subst σ ])
  func (from (gstream-natural σ)) = map (ty-ctx-subst A (naturality σ))
  naturality (from (gstream-natural σ)) {t = v} =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟨
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → ty-cong-2-2 A refl) ⟩
      map (ty-ctx-subst A _) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  func (to (gstream-natural σ)) = map (ty-ctx-subst A (sym (naturality σ)))
  naturality (to (gstream-natural σ)) {t = v} =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟨
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → ty-cong-2-2 A refl) ⟩
      map (ty-ctx-subst A _) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  eq (isoˡ (gstream-natural σ)) _ = map-inverse (λ _ → ty-ctx-subst-inverseˡ A)
  eq (isoʳ (gstream-natural σ)) _ = map-inverse (λ _ → ty-ctx-subst-inverseʳ A)

  gstream-β-head : (a : Tm Γ (constantly-ty A)) (s : Tm Γ (▻' (GStream A))) →
                   g-head (g-cons a s) ≅ᵗᵐ a
  eq (gstream-β-head a s) {x = zero}  γ = refl
  eq (gstream-β-head a s) {x = suc _} γ = refl

  gstream-β-tail : (a : Tm Γ (constantly-ty A)) (s : Tm Γ (▻' (GStream A))) →
                   g-tail (g-cons a s) ≅ᵗᵐ s
  eq (gstream-β-tail a s) {x = zero}  γ = refl
  eq (gstream-β-tail a s) {x = suc _} γ = map-inverse (λ _ → trans (ty-cong-2-1 A refl) (ty-id A))


module _ {A : Ty (now Δ)} (σ : Γ ⇒ Δ) where
  g-head-natural : (s : Tm Δ (GStream A)) →
                   (g-head s) [ σ ]'
                     ≅ᵗᵐ
                   ι[ constantly-ty-natural σ ] (g-head (ι⁻¹[ gstream-natural σ ] (s [ σ ]')))
  eq (g-head-natural s) γ = sym (trans (cong (A ⟪ tt , _ ⟫_) (map-head (s ⟨ _ , _ ⟩'))) (trans (sym (ty-comp A)) (strong-ty-id A)))

  g-tail-natural : (s : Tm Δ (GStream A)) →
                   (g-tail s) [ σ ]'
                     ≅ᵗᵐ
                   ι[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (g-tail (ι⁻¹[ gstream-natural σ ] (s [ σ ]')))
  eq (g-tail-natural s) {x = zero}  γ = refl
  eq (g-tail-natural s) {x = suc _} γ =
    sym (trans (cong (map _) first-≤-refl) (
         trans (sym (map-∘ _ _ _)) (
         trans (sym (map-∘ _ _ _)) (
         trans (cong (map _) (map-tail (s ⟨ _ , _ ⟩'))) (
         trans (sym (map-∘ _ _ _)) (map-cong (λ _ → sym (trans (trans (trans (ty-cong A refl) (ty-comp A)) (ty-comp A)) (ty-comp A))) _))))))

  g-cons-natural : (h : Tm Δ (constantly-ty A)) (t : Tm Δ (▻' (GStream A))) →
                   (g-cons h t) [ σ ]'
                     ≅ᵗᵐ
                   ι[ gstream-natural σ ] (g-cons (ι⁻¹[ constantly-ty-natural σ ] (h [ σ ]'))
                                                  (ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (t [ σ ]')))
  eq (g-cons-natural h t) {x = zero}  γ = sym (cong (_∷ []) (trans (sym (ty-comp A)) (strong-ty-id A)))
  eq (g-cons-natural h t) {x = suc _} γ = sym (cong₂ _∷_
    (trans (sym (ty-comp A)) (strong-ty-id A))
    (trans (sym (map-∘ _ _ _)) (trans (sym (map-∘ _ _ _)) (trans (sym (map-∘ _ _ _)) (
      trans (cong (map _) first-≤-refl) (map-cong (λ _ → sym (trans (trans (trans (ty-cong A refl) (ty-comp A)) (ty-comp A)) (ty-comp A))) _))))))

gstream-cong : {A : Ty (now Γ)} {A' : Ty (now Γ)} →
               A ≅ᵗʸ A' → GStream A ≅ᵗʸ GStream A'
func (from (gstream-cong A=A')) = map (func (from A=A'))
naturality (from (gstream-cong {A = A}{A' = A'} A=A')) {t = v} =
  begin
    map (A' ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (from A=A')) v))
  ≡⟨ cong (map (A' ⟪ tt , _ ⟫_)) map-first-≤ ⟨
    map (A' ⟪ tt , _ ⟫_) (map (func (from A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (λ _ → naturality (from A=A')) ⟩
    map (func (from A=A')) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
func (to (gstream-cong A=A')) = map (func (to A=A'))
naturality (to (gstream-cong {A = A}{A' = A'} A=A')) {t = v} =
  begin
    map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (to A=A')) v))
  ≡⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟨
    map (A ⟪ tt , _ ⟫_) (map (func (to A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (λ _ → naturality (to A=A')) ⟩
    map (func (to A=A')) (map (A' ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
eq (isoˡ (gstream-cong A=A')) _ = map-inverse (eq (isoˡ A=A'))
eq (isoʳ (gstream-cong A=A')) _ = map-inverse (eq (isoʳ A=A'))

module _ {A : Ty (now Γ)} where
  g-head-cong : {s s' : Tm Γ (GStream A)} → s ≅ᵗᵐ s' → g-head s ≅ᵗᵐ g-head s'
  eq (g-head-cong 𝒆) γ = cong head (eq 𝒆 γ)

  g-tail-cong : {s s' : Tm Γ (GStream A)} → s ≅ᵗᵐ s' → g-tail s ≅ᵗᵐ g-tail s'
  eq (g-tail-cong 𝒆) {x = zero}  γ = refl
  eq (g-tail-cong 𝒆) {x = suc _} γ = cong (map _ ∘ tail) (eq 𝒆 γ)

  g-cons-cong : {a a' : Tm Γ (constantly-ty A)} {s s' : Tm Γ (▻' (GStream A))} →
                a ≅ᵗᵐ a' → s ≅ᵗᵐ s' → g-cons a s ≅ᵗᵐ g-cons a' s'
  eq (g-cons-cong 𝒆a 𝒆s) {x = zero}  γ = cong (_∷ []) (eq 𝒆a γ)
  eq (g-cons-cong 𝒆a 𝒆s) {x = suc _} γ = cong₂ _∷_ (eq 𝒆a γ) (cong (map _) (eq 𝒆s γ))

module _ {A A' : Ty (now Γ)} {e : A ≅ᵗʸ A'} where
  -- Possible optimisation: the versions with ι⁻¹ can easily be
  -- derived from the versions for ι. For this purpose, we should
  -- formalise the general notion of semantic term former.
  g-head-ι : {s : Tm Γ (GStream A')} → ι[ dra-cong constantly e ] (g-head s) ≅ᵗᵐ g-head (ι[ gstream-cong e ] s)
  eq (g-head-ι {s = s}) γ = sym (map-head (s ⟨ _ , γ ⟩'))

  g-head-ι⁻¹ : {s : Tm Γ (GStream A)} → ι⁻¹[ dra-cong constantly e ] (g-head s) ≅ᵗᵐ g-head (ι⁻¹[ gstream-cong e ] s)
  eq (g-head-ι⁻¹ {s = s}) γ = sym (map-head (s ⟨ _ , γ ⟩'))

  g-tail-ι : {s : Tm Γ (GStream A')} → ι[ ▻'-cong (gstream-cong e) ] (g-tail s) ≅ᵗᵐ g-tail (ι[ gstream-cong e ] s)
  eq (g-tail-ι {s = s}) {x = zero}  γ = refl
  eq (g-tail-ι {s = s}) {x = suc _} γ = trans (map-map-cong (λ a → sym (naturality (to e))))
                                              (cong (map _) (sym (map-tail (s ⟨ _ , γ ⟩'))))

  g-tail-ι⁻¹ : {s : Tm Γ (GStream A)} → ι⁻¹[ ▻'-cong (gstream-cong e) ] (g-tail s) ≅ᵗᵐ g-tail (ι⁻¹[ gstream-cong e ] s)
  eq (g-tail-ι⁻¹ {s = s}) {x = zero}  γ = refl
  eq (g-tail-ι⁻¹ {s = s}) {x = suc _} γ = trans (map-map-cong (λ _ → sym (naturality (from e))))
                                                (cong (map _) (sym (map-tail (s ⟨ _ , γ ⟩'))))

  g-cons-ι : {a : Tm Γ (constantly-ty A')} {s : Tm Γ (▻' (GStream A'))} →
             ι[ gstream-cong e ] (g-cons a s) ≅ᵗᵐ g-cons (ι[ dra-cong constantly e ] a) (ι[ ▻'-cong (gstream-cong e) ] s)
  eq (g-cons-ι {s = s}) {x = zero}  γ = refl
  eq (g-cons-ι {s = s}) {x = suc _} γ = cong (_ ∷_) (map-map-cong (λ y → sym (naturality (to e))))

  g-cons-ι⁻¹ : {a : Tm Γ (constantly-ty A)} {s : Tm Γ (▻' (GStream A))} →
               ι⁻¹[ gstream-cong e ] (g-cons a s) ≅ᵗᵐ g-cons (ι⁻¹[ dra-cong constantly e ] a) (ι⁻¹[ ▻'-cong (gstream-cong e) ] s)
  eq (g-cons-ι⁻¹ {s = s}) {x = zero}  γ = refl
  eq (g-cons-ι⁻¹ {s = s}) {x = suc _} γ = cong (_ ∷_) (map-map-cong (λ y → sym (naturality (from e))))


gstream-closed : {A : ClosedTy ★} → IsClosedNatural A → IsClosedNatural (GStream A)
closed-natural (gstream-closed clA) σ = transᵗʸ (gstream-natural σ) (gstream-cong (closed-natural clA (now-subst σ)))
eq (from-eq (closed-id (gstream-closed {A} clA))) v =
  trans (trans (map-cong (λ a → trans (trans (cong (func (from (closed-natural clA _))) (sym (strong-ty-id A)))
                                             (eq (from-eq (closed-subst-eq clA (symˢ now-subst-id))) a))
                                      (eq (from-eq (closed-id clA)) a)) _)
               (map-id _))
        (trans (map-cong (λ _ → strong-ty-id A) v)
               (map-id v))
eq (from-eq (closed-⊚ (gstream-closed {A} clA) σ τ)) v =
  trans (cong (map _) (map-map-cong (λ _ → naturality (from (closed-natural clA (now-subst σ))))))
  (trans (sym (map-∘ _ (func (from (closed-natural clA (now-subst σ)))) _))
  (trans (map-cong (λ a → trans (eq (from-eq (closed-⊚ clA (now-subst σ) (now-subst τ))) a)
                                (trans (cong (func (from (closed-natural clA _))) (sym (strong-ty-id A)))
                                       (eq (from-eq (closed-subst-eq clA (now-subst-⊚ σ τ))) a))) _)
  (cong (map _)
  (trans (sym (map-∘ _ _ v))
  (map-cong (λ _ → ty-cong-2-1 A refl) v)))))
eq (from-eq (closed-subst-eq (gstream-closed {A} clA) ε)) v =
  trans (trans (sym (map-∘ _ _ _)) (sym (map-∘ _ _ _)))
  (trans (map-cong (λ _ → trans (cong (func (from (closed-natural clA _))) (ty-cong-2-2 A refl))
                                (eq (from-eq (closed-subst-eq clA (now-subst-cong ε))) _)) _)
  (trans (map-∘ _ _ _)
  (cong (map _ ∘ map _) first-≤-refl)))

module _ {A : ClosedTy ★} (clA : IsClosedNatural A) where
  g-cl-tail : Tm Γ (GStream A) → Tm Γ (▻ (GStream A))
  g-cl-tail s = ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] g-tail s

  g-cl-cons : Tm Γ (constantly-ty A) → Tm Γ (▻ (GStream A)) → Tm Γ (GStream A)
  g-cl-cons h t = g-cons h (ι[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] t)

module _ {A : ClosedTy ★} (clA : IsClosedNatural A) {Γ Δ : Ctx ω} (σ : Γ ⇒ Δ) where
  g-head-cl-natural : {s : Tm Δ (GStream A)} →
                      (g-head s) [ dra-closed constantly clA ∣ σ ]cl ≅ᵗᵐ g-head (s [ gstream-closed clA ∣ σ ]cl)
  g-head-cl-natural {s} =
    begin
      ι⁻¹[ transᵗʸ (constantly-ty-natural σ) (dra-cong constantly (closed-natural clA (now-subst σ))) ] ((g-head s) [ σ ]')
    ≅⟨ ι⁻¹-cong (g-head-natural σ s) ⟩
      ι⁻¹[ transᵗʸ (constantly-ty-natural σ) (dra-cong constantly (closed-natural clA (now-subst σ))) ] (ι[ constantly-ty-natural σ ]
        g-head (ι⁻¹[ gstream-natural σ ] (s [ σ ]')))
    ≅⟨ transᵗᵐ ι⁻¹-trans (ι⁻¹-cong ι-symˡ) ⟩
      ι⁻¹[ dra-cong constantly (closed-natural clA (now-subst σ)) ] g-head (ι⁻¹[ gstream-natural σ ] (s [ σ ]'))
    ≅⟨ g-head-ι⁻¹ ⟩
      g-head (ι⁻¹[ gstream-cong (closed-natural clA (now-subst σ)) ] (ι⁻¹[ gstream-natural σ ] (s [ σ ]')))
    ≅⟨ g-head-cong ι⁻¹-trans ⟨
      g-head (ι⁻¹[ closed-natural (gstream-closed clA) σ ] (s [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning

  g-tail-cl-natural : {s : Tm Δ (GStream A)} →
                      (g-cl-tail clA s) [ dra-closed later (gstream-closed clA) ∣ σ ]cl
                        ≅ᵗᵐ
                      g-cl-tail clA (s [ gstream-closed clA ∣ σ ]cl)
  g-tail-cl-natural {s} =
    begin
      ι⁻¹[ closed-natural (dra-closed later (gstream-closed clA)) σ ] (
          (ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ]
          g-tail s)
        [ σ ]')
    ≅⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟨
      ι⁻¹[ closed-natural (dra-closed later (gstream-closed clA)) σ ] (
      ι⁻¹[ ty-subst-cong-ty σ (closed-ty-eq (cl-▻'-▻ (gstream-closed clA))) ] (
      (g-tail s) [ σ ]'))
    ≅⟨ ι⁻¹-congᵉ-2-2 (closed-ty-eq-natural (cl-▻'-▻ (gstream-closed clA)) σ) ⟩
      ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] (
      ι⁻¹[ closed-natural (▻'-closed (gstream-closed clA)) σ ] (
      (g-tail s) [ σ ]'))
    ≅⟨ ι⁻¹-cong (ι⁻¹-cong (g-tail-natural σ s)) ⟩
      ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] (
      ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (transᵗʸ (gstream-natural σ) (gstream-cong (closed-natural clA (now-subst σ))))) ] (
      ι[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ]
      g-tail (ι⁻¹[ gstream-natural σ ] (s [ σ ]'))))
    ≅⟨ ι⁻¹-cong (transᵗᵐ (ι⁻¹-congᵉ (transᵉ (transᵗʸ-congʳ ▻'-cong-trans) (symᵉ transᵗʸ-assoc))) ι⁻¹-trans) ⟩
      ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] (
      ι⁻¹[ ▻'-cong (gstream-cong (closed-natural clA (now-subst σ))) ] (
      ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (
      ι[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ]
      g-tail (ι⁻¹[ gstream-natural σ ] (s [ σ ]')))))
    ≅⟨ ι⁻¹-cong (ι⁻¹-cong ι-symˡ) ⟩
      ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] (
      ι⁻¹[ ▻'-cong (gstream-cong (closed-natural clA (now-subst σ))) ]
      g-tail (ι⁻¹[ gstream-natural σ ] (s [ σ ]')))
    ≅⟨ ι⁻¹-cong g-tail-ι⁻¹ ⟩
      ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ]
      g-tail (
        ι⁻¹[ gstream-cong (closed-natural clA (now-subst σ)) ] (
        ι⁻¹[ gstream-natural σ ] (s [ σ ]')))
    ≅⟨ ι⁻¹-cong (g-tail-cong (symᵗᵐ ι⁻¹-trans)) ⟩
      ι⁻¹[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ]
      g-tail
        (ι⁻¹[ closed-natural (gstream-closed clA) σ ] (s [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning

  g-cons-cl-natural : {h : Tm Δ (constantly-ty A)} {t : Tm Δ (▻ (GStream A))} →
                      (g-cl-cons clA h t) [ gstream-closed clA ∣ σ ]cl
                        ≅ᵗᵐ
                      g-cl-cons clA (h [ dra-closed constantly clA ∣ σ ]cl) (t [ dra-closed later (gstream-closed clA) ∣ σ ]cl)
  g-cons-cl-natural {h} {t} =
    begin
      ι⁻¹[ closed-natural (gstream-closed clA) σ ] (
      (g-cons h (ι[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] t))
        [ σ ]')
    ≅⟨ ι⁻¹-cong (g-cons-natural σ h _) ⟩
      ι⁻¹[ closed-natural (gstream-closed clA) σ ] (
      ι[ gstream-natural σ ]
      g-cons (ι⁻¹[ constantly-ty-natural σ ] (h [ σ ]'))
             (ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (
               (ι[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] t) [ σ ]')))
    ≅⟨ ι-congᵉ-2-1 (transᵉ (transᵗʸ-congˡ symᵗʸ-transᵗʸ) (transᵉ transᵗʸ-assoc transᵗʸ-cancelʳ-symˡ)) ⟩
      ι⁻¹[ gstream-cong (closed-natural clA (now-subst σ)) ]
      g-cons (ι⁻¹[ constantly-ty-natural σ ] (h [ σ ]'))
             (ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (
               (ι[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] t) [ σ ]'))
    ≅⟨ g-cons-ι⁻¹ ⟩
      g-cons (ι⁻¹[ dra-cong constantly (closed-natural clA (now-subst σ)) ] (ι⁻¹[ constantly-ty-natural σ ] (h [ σ ]')))
             (ι⁻¹[ ▻'-cong (gstream-cong (closed-natural clA (now-subst σ))) ] (
               ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (
               (ι[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] t) [ σ ]')))
    ≅⟨ g-cons-cong ι⁻¹-trans (ι⁻¹-cong (ι⁻¹-cong ι-subst-commute)) ⟨
      g-cons (ι⁻¹[ closed-natural (dra-closed constantly clA) σ ] (h [ σ ]'))
             (ι⁻¹[ ▻'-cong (gstream-cong (closed-natural clA (now-subst σ))) ] (
               ι⁻¹[ transᵗʸ (▻'-natural σ) (▻'-cong (gstream-natural σ)) ] (
               ι[ ty-subst-cong-ty σ (closed-ty-eq (cl-▻'-▻ (gstream-closed clA))) ] (
               t [ σ ]'))))
    ≅⟨ g-cons-cong reflᵗᵐ (ι⁻¹-congᵉ-2-1 (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (symᵉ ▻'-cong-trans)))) ⟩
      g-cons (ι⁻¹[ closed-natural (dra-closed constantly clA) σ ] (h [ σ ]'))
             (ι⁻¹[ closed-natural (▻'-closed (gstream-closed clA)) σ ] (
               ι[ ty-subst-cong-ty σ (closed-ty-eq (cl-▻'-▻ (gstream-closed clA))) ] (
               t [ σ ]')))
    ≅⟨ g-cons-cong reflᵗᵐ (ι-congᵉ-2-2 (move-symᵗʸ-out (closed-ty-eq-natural (cl-▻'-▻ (gstream-closed clA)) σ))) ⟩
      g-cons (ι⁻¹[ closed-natural (dra-closed constantly clA) σ ] (h [ σ ]'))
             (ι[ closed-ty-eq (cl-▻'-▻ (gstream-closed clA)) ] (
               ι⁻¹[ closed-natural (dra-closed later (gstream-closed clA)) σ ] (
               t [ σ ]'))) ∎
    where open ≅ᵗᵐ-Reasoning

module _ {A : ClosedTy ★} (clA : IsClosedNatural A) {Γ : Ctx ω} where
  g-cl-tail-cong : {s1 s2 : Tm Γ (GStream A)} →
                   s1 ≅ᵗᵐ s2 →
                   g-cl-tail clA s1 ≅ᵗᵐ g-cl-tail clA s2
  g-cl-tail-cong es = ι⁻¹-cong (g-tail-cong es)

  g-cl-cons-cong : {h1 h2 : Tm Γ (constantly-ty A)} {t1 t2 : Tm Γ (▻ (GStream A))} →
                   h1 ≅ᵗᵐ h2 → t1 ≅ᵗᵐ t2 →
                   g-cl-cons clA h1 t1 ≅ᵗᵐ g-cl-cons clA h2 t2
  g-cl-cons-cong eh et = g-cons-cong eh (ι-cong et)

  gstream-cl-β-head : {h : Tm Γ (constantly-ty A)} {t : Tm Γ (▻ (GStream A))} →
                      g-head (g-cl-cons clA h t) ≅ᵗᵐ h
  gstream-cl-β-head = gstream-β-head _ _

  gstream-cl-β-tail : {h : Tm Γ (constantly-ty A)} {t : Tm Γ (▻ (GStream A))} →
                      g-cl-tail clA (g-cl-cons clA h t) ≅ᵗᵐ t
  gstream-cl-β-tail = transᵗᵐ (ι⁻¹-cong (gstream-β-tail _ _)) ι-symˡ
