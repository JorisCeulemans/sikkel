--------------------------------------------------
-- Definition of guarded streams in mode ω
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
  ≡˘⟨ map-∘ g f as ⟩
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
  ≡˘⟨ map-∘ g f as ⟩
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map id as
  ≡⟨ map-id as ⟩
    as ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Definition of guarded streams.

GStream : Ty (now Γ) → Ty Γ
GStream {Γ = Γ} A ⟨ n , γ ⟩ = Vec (timeless-ty A ⟨ n , γ ⟩) (suc n)
GStream A ⟪ m≤n , eγ ⟫ v = map (timeless-ty A ⟪ m≤n , eγ ⟫_) (first-≤ (s≤s m≤n) v)
ty-cong (GStream A) refl = map-cong (λ _ → ty-cong A refl) _
ty-id (GStream A) {t = v} =
  begin
    map (timeless-ty A ⟪ ≤-refl , _ ⟫_) (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-cong (λ _ → ty-id (timeless-ty A)) (first-≤ (s≤s ≤-refl) v) ⟩
    map id (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-id (first-≤ (s≤s ≤-refl) v) ⟩
    first-≤ (s≤s ≤-refl) v
  ≡⟨ first-≤-refl ⟩
    v ∎
  where open ≡-Reasoning
ty-comp (GStream A) {f = k≤m} {g = m≤n} {eγ-zy = eγ-nm} {eγ-yx = eγ-mk} {t = v} =
  begin
    map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s (≤-trans k≤m m≤n)) v)
  ≡⟨ cong (map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_)) first-≤-trans ⟩
    map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-cong (λ _ → ty-comp (timeless-ty A)) _ ⟩
    map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_ ∘ timeless-ty A ⟪ m≤n , eγ-nm ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-∘ (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (timeless-ty A ⟪ m≤n , eγ-nm ⟫_) _ ⟩
    map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (map (timeless-ty A ⟪ m≤n , eγ-nm ⟫_)
      (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v)))
  ≡⟨ cong (map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_)) map-first-≤ ⟩
    map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (first-≤ (s≤s k≤m)
      (map (timeless-ty A ⟪ m≤n , eγ-nm ⟫_) (first-≤ (s≤s m≤n) v))) ∎
  where open ≡-Reasoning

module _ {A : Ty (now Γ)} where
  g-head : Tm Γ (GStream A ⇛ timeless-ty A)
  _$⟨_,_⟩_ (g-head ⟨ n , γn ⟩') _ _ = head
  naturality (g-head ⟨ n , γn ⟩') {t = v} =
    begin
      head (map (timeless-ty A ⟪ _ , _ ⟫_) (first-≤ (s≤s _) v))
    ≡⟨ map-head (first-≤ (s≤s _) v) ⟩
      timeless-ty A ⟪ _ , _ ⟫ (head (first-≤ (s≤s _) v))
    ≡⟨ cong (timeless-ty A ⟪ _ , _ ⟫_) (first-≤-head v) ⟩
      timeless-ty A ⟪ _ , _ ⟫ head v ∎
    where open ≡-Reasoning
  naturality g-head m≤n eγ = to-pshfun-eq λ _ _ _ → refl

  g-tail : Tm Γ (GStream A ⇛ ▻' (GStream A))
  _$⟨_,_⟩_ (g-tail ⟨ n , γn ⟩') z≤n       _ = λ _ → _ -- = tt
  _$⟨_,_⟩_ (g-tail ⟨ n , γn ⟩') (s≤s m≤n) _ = map (timeless-ty A ⟪ n≤1+n _ , refl ⟫_) ∘ tail
  naturality (g-tail ⟨ n , γn ⟩') {ρ-xy = z≤n}     {ρ-yz = m≤n}             = refl
  naturality (g-tail ⟨ n , γn ⟩') {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} {t = v} =
    begin
      map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail (map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (first-≤ (s≤s (s≤s k≤m)) v)))
    ≡⟨ cong (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_)) (map-tail (first-≤ (s≤s (s≤s k≤m)) v)) ⟩
      map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    ≡⟨ map-map-cong (λ _ → ty-cong-2-2 (timeless-ty A) (≤-irrelevant _ _)) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    ≡⟨ cong (map (timeless-ty A ⟪ k≤m , _ ⟫_) ∘ map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_)) (first-≤-tail v) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (first-≤ (s≤s k≤m) (tail v)))
    ≡⟨ cong (map (timeless-ty A ⟪ k≤m , _ ⟫_)) map-first-≤ ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (first-≤ (s≤s k≤m) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail v))) ∎
    where open ≡-Reasoning
  naturality g-tail z≤n       eγ = to-pshfun-eq λ { z≤n _ _ → refl }
  naturality g-tail (s≤s m≤n) eγ = to-pshfun-eq λ { z≤n _ _ → refl ; (s≤s k≤m) _ _ → refl }

  prim-g-cons : Tm (Γ ,, timeless-ty A ,, (▻' (GStream A)) [ π ]) (((GStream A) [ π ]) [ π ])
  prim-g-cons ⟨ zero ,    [ [ γn , a ] , t ] ⟩' = a ∷ []
  prim-g-cons ⟨ (suc n) , [ [ γn , a ] , t ] ⟩' = a ∷ map (ty-ctx-subst A (sym (ctx-comp Γ))) t
  naturality prim-g-cons {y = zero}  z≤n       refl = refl
  naturality prim-g-cons {y = suc n} z≤n       refl = refl
  naturality prim-g-cons             (s≤s m≤n) refl = cong (timeless-ty A ⟪ s≤s m≤n , refl ⟫ _ ∷_) (sym (
    begin
      map (ty-ctx-subst A _) (map (timeless-ty A ⟪ m≤n , _ ⟫_) (first-≤ (s≤s m≤n) _))
    ≡⟨ map-map-cong (λ _ → ty-cong-2-2 A refl) ⟩
      map (timeless-ty A ⟪ s≤s m≤n , refl ⟫_) (map (ty-ctx-subst A _) (first-≤ (s≤s m≤n) _))
    ≡⟨ cong (map (timeless-ty A ⟪ s≤s m≤n , refl ⟫_)) map-first-≤ ⟩
      map (timeless-ty A ⟪ s≤s m≤n , refl ⟫_) (first-≤ (s≤s m≤n) (map (ty-ctx-subst A _) _)) ∎))
    where open ≡-Reasoning

  g-cons : Tm Γ (timeless-ty A ⇛ ▻' (GStream A) ⇛ GStream A)
  g-cons = lam (timeless-ty A) (ι[ ⇛-natural π ]
               lam (▻' (GStream A) [ π ])
                   prim-g-cons)

  gstream-natural : (σ : Δ ⇒ Γ) → (GStream A) [ σ ] ≅ᵗʸ GStream (A [ now-subst σ ])
  func (from (gstream-natural σ)) = map (ty-ctx-subst A (naturality σ))
  naturality (from (gstream-natural σ)) {t = v} =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟩
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → ty-cong-2-2 A refl) ⟩
      map (ty-ctx-subst A _) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  func (to (gstream-natural σ)) = map (ty-ctx-subst A (sym (naturality σ)))
  naturality (to (gstream-natural σ)) {t = v} =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟩
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
  ≡˘⟨ cong (map (A' ⟪ tt , _ ⟫_)) map-first-≤ ⟩
    map (A' ⟪ tt , _ ⟫_) (map (func (from A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (λ _ → naturality (from A=A')) ⟩
    map (func (from A=A')) (map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
func (to (gstream-cong A=A')) = map (func (to A=A'))
naturality (to (gstream-cong {A = A}{A' = A'} A=A')) {t = v} =
  begin
    map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (to A=A')) v))
  ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) map-first-≤ ⟩
    map (A ⟪ tt , _ ⟫_) (map (func (to A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (λ _ → naturality (to A=A')) ⟩
    map (func (to A=A')) (map (A' ⟪ tt , _ ⟫_) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
eq (isoˡ (gstream-cong A=A')) _ = map-inverse (eq (isoˡ A=A'))
eq (isoʳ (gstream-cong A=A')) _ = map-inverse (eq (isoʳ A=A'))

instance
  gstream-closed : {A : ClosedTy ★} {{_ : IsClosedNatural A}} → IsClosedNatural (GStream A)
  closed-natural {{gstream-closed}} σ = ≅ᵗʸ-trans (gstream-natural σ) (gstream-cong (closed-natural (now-subst σ)))
