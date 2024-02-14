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
    let α = _ in
    begin
      map (A ⟪ tt , α ⟫_) (first-≤ (s≤s m≤n) (map (A ⟪ tt , ctx-comp Γ ⟫_) (tail (s ⟨ suc n , γn ⟩'))))
    ≡⟨ trans (map-tail (first-≤ (s≤s (s≤s m≤n)) (map (A ⟪ tt , _ ⟫_) (s ⟨ suc n , γn ⟩')))) (
       trans (cong (map (A ⟪ tt , α ⟫_)) (first-≤-tail (map (A ⟪ tt , _ ⟫_) (s ⟨ suc n , γn ⟩')))) (
       (cong (map (A ⟪ tt , α ⟫_)) (cong (first-≤ (s≤s m≤n)) (map-tail (s ⟨ suc n , γn ⟩')))))) ⟨
      tail (map (A ⟪ tt , α ⟫_) (first-≤ (s≤s (s≤s m≤n)) (map (A ⟪ tt , ctx-comp Γ ⟫_) (s ⟨ suc n , γn ⟩'))))
    ≡⟨ cong tail (cong (map (A ⟪ tt , α ⟫_)) (map-first-≤ {m≤n = s≤s (s≤s m≤n)} {as = s ⟨ suc n , γn ⟩'})) ⟨
      tail (map (A ⟪ tt , α ⟫_) (map (A ⟪ tt , ctx-comp Γ ⟫_) (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γn ⟩'))))
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

gstream-closed : {A : ClosedTy ★} → IsClosedNatural A → IsClosedNatural (GStream A)
closed-natural (gstream-closed clA) σ = transᵗʸ (gstream-natural σ) (gstream-cong (closed-natural clA (now-subst σ)))
eq (from-eq (closed-id (gstream-closed {A} clA))) v =
  trans (trans (map-cong (λ a → trans (trans (cong (func (from (closed-natural clA _))) (sym (ty-id A)))
                                             (eq (from-eq (closed-subst-eq clA (symˢ now-subst-id))) a))
                                      (eq (from-eq (closed-id clA)) a)) _)
               (map-id _))
        (trans (map-cong (λ _ → ty-id A) v)
               (map-id v))
eq (from-eq (closed-⊚ (gstream-closed {A} clA) σ τ)) v =
  trans (cong (map _) (map-map-cong (λ _ → naturality (from (closed-natural clA (now-subst σ))))))
  (trans (sym (map-∘ _ (func (from (closed-natural clA (now-subst σ)))) _))
  (trans (map-cong (λ a → trans (eq (from-eq (closed-⊚ clA (now-subst σ) (now-subst τ))) a)
                                (trans (cong (func (from (closed-natural clA _))) (sym (ty-id A)))
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
