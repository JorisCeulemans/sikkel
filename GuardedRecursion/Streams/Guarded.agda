{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with guarded streams of natural numbers in mode ω
--
-- Note that the option omega-in-omega is used to
-- make the type GStream an instance of IsNullaryNatural.
-- This code should typecheck without this option in Agda
-- 2.6.2 once released.
--------------------------------------------------

module GuardedRecursion.Streams.Guarded where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec hiding ([_]; _⊛_)
-- open import Data.Vec.Properties
import Data.Vec.Relation.Binary.Pointwise.Inductive as Vec
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Level renaming (zero to lzero; suc to lsuc)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import GuardedRecursion.Modalities
open import Reflection.Naturality
open import Reflection.Naturality.Instances
open import Reflection.Naturality.GuardedRecursion.Instances
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.LobInduction

private
  variable
    ℓa ℓb ℓc r : Level
    Γ Δ : Ctx ω ℓ r


--------------------------------------------------
-- Some basic operations and proofs regarding vectors

first-≤ : ∀ {m n} {A : Set ℓ} → m ≤ n → Vec A n → Vec A m
first-≤ z≤n       as       = []
first-≤ (s≤s m≤n) (a ∷ as) = a ∷ first-≤ m≤n as

open import Relation.Binary using (REL; Rel; Reflexive)

first-≤-cong : ∀ {a b ℓ} {A : Set a} {B : Set b} {_∼_ : REL A B ℓ}
               {m n} (m≤n : m ≤ n) {xs : Vec A n} {ys : Vec B n} →
               Vec.Pointwise _∼_ xs ys → Vec.Pointwise _∼_ (first-≤ m≤n xs) (first-≤ m≤n ys)
first-≤-cong z≤n       xs~ys             = Vec.[]
first-≤-cong (s≤s m≤n) (x∼y Vec.∷ xs∼ys) = x∼y Vec.∷ first-≤-cong m≤n xs∼ys

map⁺ˡ : ∀ {a b c ℓ} {A : Set a} {B : Set b} {C : Set c}
        {_∼_ : REL B C ℓ} {f : A → B} {g : A → C} →
        (∀ {x} → f x ∼ g x) → {n : ℕ} → {xs : Vec A n} →
        Vec.Pointwise _∼_ (map f xs) (map g xs)
map⁺ˡ f∼g {xs = []}     = Vec.[]
map⁺ˡ f∼g {xs = x ∷ xs} = f∼g Vec.∷ map⁺ˡ f∼g

map⁺ʳ : ∀ {a b ℓ ℓ'} {A : Set a} {B : Set b}
        {_∼₁_ : Rel A ℓ} {_∼₂_ : Rel B ℓ'} {f : A → B} →
        (∀ {x y} → x ∼₁ y → f x ∼₂ f y) → {n : ℕ} → {xs ys : Vec A n} →
        Vec.Pointwise _∼₁_ xs ys → Vec.Pointwise _∼₂_ (map f xs) (map f ys)
map⁺ʳ f-cong Vec.[]            = Vec.[]
map⁺ʳ f-cong (x∼y Vec.∷ xs∼ys) = f-cong x∼y Vec.∷ map⁺ʳ f-cong xs∼ys

first-≤-refl : ∀ {a ℓ n} {A : Set a} {_∼_ : Rel A ℓ} →
               Reflexive _∼_ → {as : Vec A n} → Vec.Pointwise _∼_ (first-≤ (≤-refl) as) as
first-≤-refl rfl {as = []}     = Vec.[]
first-≤-refl rfl {as = a ∷ as} = rfl Vec.∷ first-≤-refl rfl

map-id : ∀ {a ℓ n} {A : Set a} {_∼_ : Rel A ℓ} →
         Reflexive _∼_ → {as : Vec A n} → Vec.Pointwise _∼_ (map id as) as
map-id rfl {as = []}     = Vec.[]
map-id rfl {as = a ∷ as} = rfl Vec.∷ map-id rfl

first-≤-trans : ∀ {a ℓ k m n} {A : Set a} {_∼_ : Rel A ℓ} → Reflexive _∼_ →
                (k≤m : k ≤ m) (m≤n : m ≤ n) (as : Vec A n) →
                Vec.Pointwise _∼_ (first-≤ (≤-trans k≤m m≤n) as) (first-≤ k≤m (first-≤ m≤n as))
first-≤-trans rfl z≤n       m≤n       as       = Vec.[]
first-≤-trans rfl (s≤s k≤m) (s≤s m≤n) (a ∷ as) = rfl Vec.∷ first-≤-trans rfl k≤m m≤n as

map-∘ : ∀ {a b c ℓ n} {A : Set a} {B : Set b} {C : Set c} {_∼_ : Rel C ℓ} → Reflexive _∼_ →
        (f : B → C) (g : A → B) →
        {as : Vec A n} → Vec.Pointwise _∼_ (map (f ∘ g) as) (map f (map g as))
map-∘ rfl f g {[]}     = Vec.[]
map-∘ rfl f g {a ∷ as} = rfl Vec.∷ map-∘ rfl f g

map-first-≤ : ∀ {a b m n ℓ} {A : Set a} {B : Set b} {_∼_ : Rel B ℓ} → Reflexive _∼_ →
              (f : A → B) (m≤n : m ≤ n) (as : Vec A n) →
              Vec.Pointwise _∼_ (map f (first-≤ m≤n as)) (first-≤ m≤n (map f as))
map-first-≤ rfl f z≤n       as       = Vec.[]
map-first-≤ rfl f (s≤s m≤n) (a ∷ as) = rfl Vec.∷ map-first-≤ rfl f m≤n as

map-head : ∀ {a b ℓ n} {A : Set a} {B : Set b} {_∼_ : Rel B ℓ} → Reflexive _∼_ →
           (f : A → B) (as : Vec A (suc n)) →
           head (map f as) ∼ f (head as)
map-head rfl f (a ∷ as) = rfl

first-≤-head : ∀ {a ℓ m n} {A : Set a} {_∼_ : Rel A ℓ} → Reflexive _∼_ →
               (m≤n : m ≤ n) (as : Vec A (suc n)) →
               head (first-≤ (s≤s m≤n) as) ∼ head as
first-≤-head rfl m≤n (a ∷ as) = rfl

map-tail : ∀ {a b ℓ n} {A : Set a} {B : Set b} {_∼_ : Rel B ℓ} → Reflexive _∼_ →
           (f : A → B) (as : Vec A (suc n)) →
           Vec.Pointwise _∼_ (tail (map f as)) (map f (tail as))
map-tail rfl f (a ∷ as) = Vec.refl rfl

map-map-cong : ∀ {a b c d ℓ n} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
               {_∼_ : Rel D ℓ} →
               {f : A → B} {g : B → D} {f' : A → C} {g' : C → D}
               (e : ∀ {x} → g (f x) ∼ g' (f' x))
               (as : Vec A n) →
               Vec.Pointwise _∼_ (map g (map f as)) (map g' (map f' as))
map-map-cong e []       = Vec.[]
map-map-cong e (x ∷ as) = e Vec.∷ map-map-cong e as

first-≤-tail : ∀ {a ℓ m n} {A : Set a} {_∼_ : Rel A ℓ} → Reflexive _∼_ →
               (m≤n : m ≤ n) (as : Vec A (suc n)) →
               Vec.Pointwise _∼_ (tail (first-≤ (s≤s m≤n) as)) (first-≤ m≤n (tail as))
first-≤-tail rfl m≤n (a ∷ as) = Vec.refl rfl
{-
map-inverse : ∀ {n} {A : Set ℓ} {B : Set ℓ'}
              {f : A → B} {g : B → A} (e : g ∘ f ≗ id)
              (as : Vec A n) →
              map g (map f as) ≡ as
map-inverse {f = f}{g} e as =
  begin
    map g (map f as)
  ≡˘⟨ map-∘ g f as ⟩
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map id as
  ≡⟨ map-id as ⟩
    as ∎
  where open ≡-Reasoning
-}

--------------------------------------------------
-- Definition of guarded streams.

GStream : Ty (now Γ) ℓ r → Ty Γ ℓ (ℓ ⊔ r)
type (GStream A) n γ = Vec.setoid (type (timeless-ty A) n γ) (suc n)
morph (GStream A) m≤n eγ v = map (timeless-ty A ⟪ m≤n , eγ ⟫_) (first-≤ (s≤s m≤n) v)
morph-cong (GStream A) m≤n eγ ev = Vec.map⁺ (morph-cong (timeless-ty A) m≤n eγ) (first-≤-cong (s≤s m≤n) ev)
morph-hom-cong (GStream A) refl = map⁺ˡ (morph-hom-cong A refl)
morph-id (GStream A) v =
  begin
    map (timeless-ty A ⟪ ≤-refl , _ ⟫_) (first-≤ (s≤s ≤-refl) v)
  ≈⟨ Vec.map⁺ (ty≈-trans A (morph-id (timeless-ty A) _)) (first-≤-refl (ty≈-refl (timeless-ty A))) ⟩
    map id v
  ≈⟨ map-id (ty≈-refl (timeless-ty A)) ⟩
    v ∎
  where open SetoidReasoning (type (GStream A) _ _)
morph-comp (GStream A) k≤m m≤n eγ-nm eγ-mk v =
  begin
    map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s (≤-trans k≤m m≤n)) v)
  ≈⟨ Vec.map⁺ (ty≈-trans (timeless-ty A) (morph-comp (timeless-ty A) k≤m m≤n eγ-nm eγ-mk _))
              (first-≤-trans (ty≈-refl (timeless-ty A)) (s≤s k≤m) (s≤s m≤n) v) ⟩
    map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_ ∘ timeless-ty A ⟪ m≤n , eγ-nm ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≈⟨ map-∘ (ty≈-refl (timeless-ty A)) _ _ ⟩
    map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (map (timeless-ty A ⟪ m≤n , eγ-nm ⟫_)
      (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v)))
  ≈⟨ Vec.map⁺ (morph-cong (timeless-ty A) k≤m eγ-mk)
              (map-first-≤ (ty≈-refl (timeless-ty A)) _ (s≤s k≤m) (first-≤ (s≤s m≤n) v)) ⟩
    map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (first-≤ (s≤s k≤m)
      (map (timeless-ty A ⟪ m≤n , eγ-nm ⟫_) (first-≤ (s≤s m≤n) v))) ∎
  where open SetoidReasoning (type (GStream A) _ _)

module _ {A : Ty (now Γ) ℓ r} where
  g-head : Tm Γ (GStream A ⇛ timeless-ty A)
  _$⟨_,_⟩_ (term g-head n γn) _ _ = head
  $-cong (term g-head n γn) _ _ {x = _ ∷ _} {y = _ ∷ _} = Vec.head
  $-hom-cong (term g-head n γn) _ = ty≈-refl (timeless-ty A)
  naturality (term g-head n γn) {x = k} {y = m} {ρ-xy = k≤m} {γx = γk} {γy = γm} eγ-nm eγ-mk v =
    begin
      head (map (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (first-≤ (s≤s k≤m) v))
    ≈⟨ map-head {_∼_ = ty≈ (timeless-ty A) k γk} (ty≈-refl (timeless-ty A)) (timeless-ty A ⟪ k≤m , eγ-mk ⟫_) (first-≤ (s≤s k≤m) v) ⟩
      timeless-ty A ⟪ k≤m , eγ-mk ⟫ head (first-≤ (s≤s k≤m) v)
    ≈⟨ morph-cong (timeless-ty A) k≤m eγ-mk (first-≤-head {_∼_ = ty≈ (timeless-ty A) m γm} (ty≈-refl (timeless-ty A)) k≤m v) ⟩
      timeless-ty A ⟪ k≤m , eγ-mk ⟫ head v ∎
    where open SetoidReasoning (type (timeless-ty A) k γk)
  naturality g-head _ _ _ _ _ = ty≈-refl (timeless-ty A)

  g-tail : Tm Γ (GStream A ⇛ ▻' (GStream A))
  _$⟨_,_⟩_ (term g-tail n γn) z≤n       _ = λ _ → tt
  _$⟨_,_⟩_ (term g-tail n γn) (s≤s m≤n) _ = map (timeless-ty A ⟪ n≤1+n _ , ctx≈-refl Γ ⟫_) ∘ tail
  $-cong (term g-tail n γn) z≤n       _                        _  = tt
  $-cong (term g-tail n γn) (s≤s m≤n) _ {x = _ ∷ _}{y = _ ∷ _} et = map⁺ʳ (morph-cong (timeless-ty A) _ _) (Vec.tail et)
  $-hom-cong (term g-tail n γn) {ρ = z≤n}     e    = tt
  $-hom-cong (term g-tail n γn) {ρ = s≤s m≤n} refl = ty≈-refl (GStream A)
  naturality (term g-tail n γn) {ρ-xy = z≤n}     {ρ-yz = m≤n} _ _ _ = tt
  naturality (term g-tail n γn) {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} eγ-nm eγ-mk v =
    begin
      map (timeless-ty A ⟪ n≤1+n _ , ctx≈-refl Γ ⟫_) (tail (map (timeless-ty A ⟪ s≤s k≤m , eγ-mk ⟫_) (first-≤ (s≤s (s≤s k≤m)) v)))
    ≈⟨ map⁺ʳ (morph-cong (timeless-ty A) _ (ctx≈-refl Γ)) (map-tail (ty≈-refl (timeless-ty A)) _ (first-≤ (s≤s (s≤s k≤m)) v)) ⟩
      map (timeless-ty A ⟪ n≤1+n _ , ctx≈-refl Γ ⟫_) (map (timeless-ty A ⟪ s≤s k≤m , eγ-mk ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    ≈⟨ map-map-cong (morph-hom-cong-2-2 (timeless-ty A) (≤-irrelevant _ _)) (tail (first-≤ (s≤s (s≤s k≤m)) v)) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    ≈⟨ map⁺ʳ (morph-cong (timeless-ty A) k≤m _) (map⁺ʳ (morph-cong (timeless-ty A) (n≤1+n _) _) (first-≤-tail (ty≈-refl (timeless-ty A)) (s≤s k≤m) v)) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (first-≤ (s≤s k≤m) (tail v)))
    ≈⟨ map⁺ʳ (morph-cong (timeless-ty A) k≤m _) (map-first-≤ (ty≈-refl (timeless-ty A)) _ (s≤s k≤m) (tail v)) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (first-≤ (s≤s k≤m) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail v))) ∎
    where open SetoidReasoning (type (GStream A) _ (Γ ⟪ n≤1+n _ ⟫ _))
  naturality g-tail z≤n       _ z≤n       _ _ = tt
  naturality g-tail (s≤s m≤n) _ z≤n       _ _ = tt
  naturality g-tail (s≤s m≤n) _ (s≤s k≤m) _ _ = ty≈-refl (GStream A)
  
  g-cons : Tm Γ (timeless-ty A ⊠ ▻' (GStream A) ⇛ GStream A)
  term g-cons n γn $⟨ z≤n ,     _ ⟩ [ h , _ ] = h ∷ []
  term g-cons n γn $⟨ s≤s m≤n , _ ⟩ [ h , t ] = h ∷ map (ctx-element-subst A (ctx≈-sym Γ (rel-comp Γ z≤n (n≤1+n _) _))) t
  $-cong (term g-cons n γn) z≤n       _ [ eh , et ] = eh Vec.∷ Vec.[]
  $-cong (term g-cons n γn) (s≤s m≤n) _ [ eh , et ] = eh Vec.∷ map⁺ʳ (morph-cong A _ _) et
  $-hom-cong (term g-cons n γn) {ρ = z≤n}     refl = ty≈-refl (GStream A)
  $-hom-cong (term g-cons n γn) {ρ = s≤s m≤n} refl = ty≈-refl (GStream A)
  naturality (term g-cons n γn)             {ρ-xy = z≤n}     {ρ-yz = z≤n}     _ _ _         = ty≈-refl (GStream A)
  naturality (term g-cons n γn)             {ρ-xy = z≤n}     {ρ-yz = s≤s m≤n} _ _ _         = ty≈-refl (GStream A)
  naturality (term g-cons n γn) {x = suc k} {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} _ _ [ a , v ] = ty≈-refl A Vec.∷
    (begin
      map (ctx-element-subst A _) (map (timeless-ty A ⟪ k≤m , _ ⟫_) (first-≤ (s≤s k≤m) v))
    ≈⟨ map-map-cong (morph-hom-cong-2-2 A refl) (first-≤ (s≤s k≤m) v) ⟩
      map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (map (ctx-element-subst A _) (first-≤ (s≤s k≤m) v))
    ≈⟨ map⁺ʳ (morph-cong (timeless-ty A) (s≤s k≤m) _) (map-first-≤ (ty≈-refl (timeless-ty A)) _ (s≤s k≤m) v) ⟩
      map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (first-≤ (s≤s k≤m) (map (ctx-element-subst A _) v)) ∎)
    where open SetoidReasoning (Vec.setoid (type (timeless-ty A) (suc k) _) (suc k))
  naturality g-cons z≤n       _ z≤n       _ _ = ty≈-refl (GStream A)
  naturality g-cons (s≤s m≤n) _ z≤n       _ _ = ty≈-refl (GStream A)
  naturality g-cons (s≤s m≤n) _ (s≤s k≤m) _ _ = ty≈-refl (GStream A)
{-
  gstream-natural : (σ : Δ ⇒ Γ) → (GStream A) [ σ ] ≅ᵗʸ GStream (A [ now-subst σ ])
  func (from (gstream-natural σ)) = map (ctx-element-subst A (naturality σ _))
  naturality (from (gstream-natural σ)) v =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 A refl) (first-≤ (s≤s _) v) ⟩
      map (ctx-element-subst A _) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  func (to (gstream-natural σ)) = map (ctx-element-subst A (sym (naturality σ _)))
  naturality (to (gstream-natural σ)) v =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 A refl) (first-≤ (s≤s _) v) ⟩
      map (ctx-element-subst A _) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  eq (isoˡ (gstream-natural σ)) = map-inverse (ctx-element-subst-inverseˡ A)
  eq (isoʳ (gstream-natural σ)) = map-inverse (ctx-element-subst-inverseʳ A)

gstream-cong : {A : Ty (now Γ) ℓ} {A' : Ty (now Γ) ℓ'} →
               A ≅ᵗʸ A' → GStream A ≅ᵗʸ GStream A'
func (from (gstream-cong A=A')) = map (func (from A=A'))
naturality (from (gstream-cong {A = A}{A' = A'} A=A')) v =
  begin
    map (A' ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (from A=A')) v))
  ≡˘⟨ cong (map (A' ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
    map (A' ⟪ tt , _ ⟫_) (map (func (from A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (naturality (from A=A')) (first-≤ (s≤s _) v) ⟩
    map (func (from A=A')) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
func (to (gstream-cong A=A')) = map (func (to A=A'))
naturality (to (gstream-cong {A = A}{A' = A'} A=A')) v =
  begin
    map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (to A=A')) v))
  ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
    map (A ⟪ tt , _ ⟫_) (map (func (to A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (naturality (to A=A')) (first-≤ (s≤s _) v) ⟩
    map (func (to A=A')) (map (A' ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
eq (isoˡ (gstream-cong A=A')) = map-inverse (eq (isoˡ A=A'))
eq (isoʳ (gstream-cong A=A')) = map-inverse (eq (isoʳ A=A'))


--------------------------------------------------
-- Declaration needed for the naturality solver
-- This shows that it is easy to extend the solver to work with custom types
-- and type operations (even the ones that are only definable in a particular
-- base category).

instance
  gstream-un : IsUnaryNatural GStream
  natural-un {{gstream-un}} σ = gstream-natural σ
  cong-un {{gstream-un}} = gstream-cong


--------------------------------------------------
-- Some operations on guarded streams
--
-- Most functions are an implementation of the examples on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The guarded lambda-calculus: Programming and reasoning with guarded recursion for coinductive types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.

open import Reflection.Tactic.Naturality

module _ {A : NullaryTypeOp ★ ℓa} {{_ : IsNullaryNatural A}} where
  
  g-snd : Tm Γ (GStream A ⇛ ▻' (timeless-ty A))
  g-snd = nlamι[ "s" ∈ GStream A ] g-head ⟨$⟩' (g-tail $ nvarι "s")

  g-thrd : Tm Γ (GStream A ⇛ ▻' (▻' (timeless-ty A)))
  g-thrd = nlamι[ "s" ∈ GStream A ] g-snd ⟨$⟩' (g-tail $ nvarι "s")

g-zeros : Tm Γ (GStream Nat')
g-zeros = nlöbι[ "s" ∈ GStream Nat' ] g-cons $ pair (timeless-tm zero') (nvarι "s")

private
  module _ {Γ : Ctx ω ℓ} where
    zeros-test : g-head {Γ = Γ} $ g-zeros ≅ᵗᵐ timeless-tm zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : g-snd {Γ = Γ} $ g-zeros ≅ᵗᵐ next' (timeless-tm zero')
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

g-map : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} {B : NullaryTypeOp ★ ℓ'} {{_ : IsNullaryNatural B}} →
        Tm Γ (timeless-ty (A ⇛ B) ⇛ GStream A ⇛ GStream B)
g-map {A = A}{B = B} =
  nlamι[ "f" ∈ timeless-ty (A ⇛ B) ]
    nlöbι[ "m" ∈ GStream A ⇛ GStream B ]
      nlamι[ "s" ∈ GStream A ]
        g-cons $ pair (timeless-tm (untimeless-tm (nvarι "f") $ untimeless-tm (g-head $ nvarι "s")))
                      (nvarι "m" ⊛' (g-tail $ nvarι "s"))

g-iterate : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} →
            Tm Γ (timeless-ty (A ⇛ A) ⇛ timeless-ty A ⇛ GStream A)
g-iterate {A = A} =
  nlamι[ "f" ∈ timeless-ty (A ⇛ A) ]
    nlöbι[ "g" ∈ timeless-ty A ⇛ GStream A ]
      nlamι[ "x" ∈ timeless-ty A ]
        g-cons $ pair (nvarι "x")
                      (nvarι "g" ⊛' next' (timeless-tm (untimeless-tm (nvarι "f") $ untimeless-tm (nvarι "x"))))

g-iterate' : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} →
             Tm Γ (timeless-ty (A ⇛ A) ⇛ timeless-ty A ⇛ GStream A)
g-iterate' {A = A} =
  nlamι[ "f" ∈ timeless-ty (A ⇛ A) ]
    nlamι[ "a" ∈ timeless-ty A ]
      nlöbι[ "s" ∈ GStream A ]
        g-cons $ pair (nvarι "a")
                      (next' (g-map $ nvarι "f") ⊛' nvarι "s")

suc-func : {Γ : Ctx ★ ℓ} → Tm Γ (Nat' ⇛ Nat')
suc-func = discr-func suc

g-nats : Tm Γ (GStream Nat')
g-nats = g-iterate' $ timeless-tm suc-func $ timeless-tm zero'

private
  module _ {Γ : Ctx ω ℓ} where
    nats-test : g-head {Γ = Γ} $ g-nats ≅ᵗᵐ timeless-tm zero'
    eq nats-test {x = zero}  _ = refl
    eq nats-test {x = suc n} _ = refl

    nats-test2 : g-snd {Γ = Γ} $ g-nats ≅ᵗᵐ next' (timeless-tm (suc' zero'))
    eq nats-test2 {x = zero}        _ = refl
    eq nats-test2 {x = suc zero}    _ = refl
    eq nats-test2 {x = suc (suc n)} _ = refl

    nats-test3 : g-thrd {Γ = Γ} $ g-nats ≅ᵗᵐ next' (next' (timeless-tm (suc' (suc' zero'))))
    eq nats-test3 {x = zero}              _ = refl
    eq nats-test3 {x = suc zero}          _ = refl
    eq nats-test3 {x = suc (suc zero)}    _ = refl
    eq nats-test3 {x = suc (suc (suc n))} _ = refl

    map-test : g-head {Γ = Γ} $ (g-map $ timeless-tm suc-func $ g-zeros) ≅ᵗᵐ timeless-tm (discr 1)
    eq map-test {x = zero}  _ = refl
    eq map-test {x = suc x} _ = refl

    map-test2 : g-thrd {Γ = Γ} $ (g-map $ timeless-tm suc-func $ (g-map $ timeless-tm suc-func $ g-nats))
                ≅ᵗᵐ next' (next' (timeless-tm ((discr 4))))
    eq map-test2 {x = zero}              _ = refl
    eq map-test2 {x = suc zero}          _ = refl
    eq map-test2 {x = suc (suc zero)}    _ = refl
    eq map-test2 {x = suc (suc (suc n))} _ = refl

g-interleave : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} →
               Tm Γ (GStream A ⇛ ▻' (GStream A) ⇛ GStream A)
g-interleave {A = A} =
  nlöbι[ "g" ∈ GStream A ⇛ ▻' (GStream A) ⇛ GStream A ]
    nlamι[ "s" ∈ GStream A ]
      nlamι[ "t" ∈ ▻' (GStream A) ]
        g-cons $ pair (g-head $ nvarι "s")
                      (nvarι "g" ⊛' nvarι "t" ⊛' next' (g-tail $ nvarι "s"))

one' : {Γ : Ctx ★ ℓ} → Tm Γ Nat'
one' = suc' zero'

g-toggle : Tm Γ (GStream Nat')
g-toggle = nlöbι[ "s" ∈ GStream Nat' ]
             g-cons $ pair (timeless-tm one')
                           (next' (g-cons $ pair (timeless-tm zero') (nvarι "s")))

g-paperfolds : Tm Γ (GStream Nat')
g-paperfolds = nlöbι[ "s" ∈ GStream Nat' ] g-interleave $ g-toggle $ nvarι "s"

{-
module _ (T-op : NullaryTypeOp ω ℓ) {{_ : IsNullaryNatural T-op}} where
  T : Ty Γ ℓ
  T = ⟦ nul T-op ⟧exp

  g-initial : Tm Γ ((Nat' ⊠ ▻' T ⇛ T) ⇛ GStream ⇛ T)
  g-initial = löbι ((Nat' ⊠ ▻' T ⇛ T) ⇛ GStream ⇛ T)
                   (lamι (Nat' ⊠ ▻' T ⇛ T)
                         (lamι GStream
                               (varι 1 $ (pair (g-head $ varι 0)
                                               (varι 2 ⊛' next' (varι 1) ⊛' (g-tail $ varι 0))))))

  g-final : Tm Γ ((T ⇛ Nat' ⊠ ▻' T) ⇛ T ⇛ GStream)
  g-final = löbι ((T ⇛ Nat' ⊠ ▻' T) ⇛ T ⇛ GStream)
                 (lamι (T ⇛ Nat' ⊠ ▻' T)
                       (lamι T let x = varι 1 $ varι 0
                               in g-cons $ (pair (fst x)
                                                 (varι 2 ⊛' next' (varι 1) ⊛' snd x))))
-}

module _
  {A : NullaryTypeOp ★ ℓa} {{_ : IsNullaryNatural A}}
  {B : NullaryTypeOp ★ ℓb} {{_ : IsNullaryNatural B}}
  {C : NullaryTypeOp ★ ℓc} {{_ : IsNullaryNatural C}}
  where

  -- This is an implementation of an example on page 3 of the paper
  --   Robert Atkey, and Conor McBride.
  --   Productive Coprogramming with Guarded Recursion.
  --   ICFP 2013.
  g-mergef : Tm Γ (timeless-ty A ⇛ timeless-ty B ⇛ ▻' (GStream C) ⇛ GStream C) →
             Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
  g-mergef f = nlöbι[ "g" ∈ GStream A ⇛ GStream B ⇛ GStream C ]
                 nlamι[ "xs" ∈ GStream A ]
                   nlamι[ "ys" ∈ GStream B ]
                     (↑ι⟨ 3 ⟩ f) $ (g-head $ nvarι "xs")
                                 $ (g-head $ nvarι "ys")
                                 $ (nvarι "g" ⊛' (g-tail $ nvarι "xs") ⊛' (g-tail $ nvarι "ys"))

  -- Examples that were not taken from a paper.
  g-zipWith : Tm Γ (timeless-ty (A ⇛ B ⇛ C)) →
              Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
  g-zipWith f = g-mergef (
    nlamι[ "x" ∈ timeless-ty A ]
      nlamι[ "y" ∈ timeless-ty B ]
        nlamι[ "zs" ∈ ▻' (GStream C) ]
          g-cons $ pair (timeless-tm (untimeless-tm (↑ι⟨ 3 ⟩ f) $ untimeless-tm (nvarι "x")
                                                                $ untimeless-tm (nvarι "y")))
                        (nvarι "zs"))

prim-nat-sum : {Γ : Ctx ★ ℓ} → Tm Γ Nat' → Tm Γ Nat' → Tm Γ Nat'
term (prim-nat-sum t s) n γ = t ⟨ n , γ ⟩' + s ⟨ n , γ ⟩'
naturality (prim-nat-sum t s) m≤n eγ = cong₂ _+_ (naturality t m≤n eγ) (naturality s m≤n eγ)

nat-sum : {Γ : Ctx ★ ℓ} → Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = nlamι[ "m" ∈ Nat' ] nlamι[ "n" ∈ Nat' ] prim-nat-sum (nvarι "m") (nvarι "n")

pair' : Tm Γ (timeless-ty Nat' ⇛ ▻' (GStream Nat') ⇛ timeless-ty Nat' ⊠ ▻' (GStream Nat'))
pair' = nlamι[ "x" ∈ timeless-ty Nat' ] nlamι[ "y" ∈ ▻' (GStream Nat') ] pair (nvarι "x") (nvarι "y")

g-fibs : Tm Γ (GStream Nat')
g-fibs = nlöbι[ "s" ∈ GStream Nat' ]
  g-cons $ pair (timeless-tm one') (
  g-cons ⟨$⟩' ((pair' $ timeless-tm one') ⟨$⟩' (
  (f $ nvarι "s") ⟨$⟩' (g-tail ⟨$⟩' nvarι "s"))))
  where
    f : Tm Γ (▻' (GStream Nat') ⇛ ▻' (GStream Nat') ⇛ ▻' (GStream Nat'))
    f = nlamι[ "ms" ∈ ▻' (GStream Nat') ]
          nlamι[ "ns" ∈ ▻' (GStream Nat') ]
            g-zipWith (timeless-tm nat-sum) ⟨$⟩' nvarι "ms" ⊛' nvarι "ns"

private
  module _ {Γ : Ctx ω ℓ} where
    fibs-test : g-thrd {Γ = Γ} $ g-fibs ≅ᵗᵐ next' (next' (timeless-tm (discr 2)))
    eq fibs-test {x = zero} _ = refl
    eq fibs-test {x = suc zero} _ = refl
    eq fibs-test {x = suc (suc zero)} _ = refl
    eq fibs-test {x = suc (suc (suc x))} _ = refl
-}
