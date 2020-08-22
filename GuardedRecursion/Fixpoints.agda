-- Work in progress on constructing fixpoints for locally contractive functors, following
-- "First Steps in Synthetic Guarded Domain Theory: Step-indexing in the Topos of Trees" by
-- Birkedal et al.

module GuardedRecursion.Fixpoints where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic
open import Function using (_∘_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding (naturality)

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import GuardedRecursion.Later


record isStrongFunctor (F : ∀ {ℓt} → Ty {C = ω} ◇ ℓt → Ty {C = ω} ◇ ℓt) : Setω where
  field
    map : ∀ {ℓt ℓs} {T : Ty ◇ ℓt} {S : Ty ◇ ℓs} →
          (T ↣ S) → (F T ↣ F S)
    map-cong : ∀ {ℓt ℓs} {T : Ty ◇ ℓt} {S : Ty ◇ ℓs} {η φ : T ↣ S} →
               η ≅ⁿ φ → map η ≅ⁿ map φ
    map-id : ∀ {ℓt} {T : Ty ◇ ℓt} →
             map (id-trans T) ≅ⁿ id-trans (F T)
    map-comp : ∀ {ℓr ℓs ℓt} {R : Ty ◇ ℓr} {S : Ty ◇ ℓs} {T : Ty ◇ ℓt} →
               (η : S ↣ T) (φ : R ↣ S) →
               map (η ⊙ φ) ≅ⁿ map η ⊙ map φ
    strength : ∀ {ℓt ℓs} {T : Ty ◇ ℓt} {S : Ty ◇ ℓs} →
               (T ⇛ S) ↣ (F (▻' T) ⇛ F (▻' S))

module _
  (F : ∀ {ℓt} → Ty ◇ ℓt → Ty ◇ ℓt)
  (sf : isStrongFunctor F)
  where

  open isStrongFunctor sf

  𝑋-type : ℕ → Ty {C = ω} ◇ 0ℓ
  𝑋-type zero    = F (▻' Unit')
  𝑋-type (suc n) = F (▻' (𝑋-type n))

  𝑋-nattrans : {m n : ℕ} (m≤n : m ≤ n) → (𝑋-type n ↣ 𝑋-type m)
  𝑋-nattrans {n = zero } z≤n = id-trans (𝑋-type zero)
  𝑋-nattrans {n = suc n} z≤n = map (▻'-map !Unit)
  𝑋-nattrans (s≤s m≤n) = map (▻'-map (𝑋-nattrans m≤n))

  𝑋-nattrans-id : {n : ℕ} → 𝑋-nattrans (≤-refl {n}) ≅ⁿ id-trans (𝑋-type n)
  𝑋-nattrans-id {zero } = ≅ⁿ-refl
  𝑋-nattrans-id {suc n} =
    begin
      map (▻'-map (𝑋-nattrans (≤-refl {n})))
    ≅⟨ map-cong (▻'-map-cong (𝑋-nattrans-id {n})) ⟩
      map (▻'-map (id-trans (𝑋-type n)))
    ≅⟨ map-cong ▻'-map-id ⟩
      map (id-trans (▻' (𝑋-type n)))
    ≅⟨ map-id ⟩
      id-trans (F (▻' (𝑋-type n))) ∎
    where open ≅ⁿ-Reasoning

  𝑋-nattrans-comp : {k m n : ℕ} (k≤m : k ≤ m) (m≤n : m ≤ n) →
                    𝑋-nattrans (≤-trans k≤m m≤n) ≅ⁿ 𝑋-nattrans k≤m ⊙ 𝑋-nattrans m≤n
  𝑋-nattrans-comp z≤n z≤n = ≅ⁿ-sym (⊙-id-transˡ _)
  𝑋-nattrans-comp z≤n (s≤s m≤n) =
    begin
      map (▻'-map !Unit)
    ≅˘⟨ map-cong (▻'-map-cong (Unit-terminal _)) ⟩
      map (▻'-map (!Unit ⊙ (𝑋-nattrans m≤n)))
    ≅⟨ map-cong (▻'-map-comp _ _) ⟩
      map (▻'-map !Unit ⊙ ▻'-map (𝑋-nattrans m≤n))
    ≅⟨ map-comp _ _ ⟩
      map (▻'-map !Unit) ⊙ map (▻'-map (𝑋-nattrans m≤n)) ∎
    where open ≅ⁿ-Reasoning
  𝑋-nattrans-comp (s≤s k≤m) (s≤s m≤n) =
    begin
      map (▻'-map (𝑋-nattrans (≤-trans k≤m m≤n)))
    ≅⟨ map-cong (▻'-map-cong (𝑋-nattrans-comp k≤m m≤n)) ⟩
      map (▻'-map (𝑋-nattrans k≤m ⊙ 𝑋-nattrans m≤n))
    ≅⟨ map-cong (▻'-map-comp _ _) ⟩
      map (▻'-map (𝑋-nattrans k≤m) ⊙ ▻'-map (𝑋-nattrans m≤n))
    ≅⟨ map-comp _ _ ⟩
      map (▻'-map (𝑋-nattrans k≤m)) ⊙ map (▻'-map (𝑋-nattrans m≤n)) ∎
    where open ≅ⁿ-Reasoning

  𝑋 : Ty {C = ω} ◇ 0ℓ
  type 𝑋 n _ = 𝑋-type n ⟨ n , _ ⟩
  morph 𝑋 {y = n} m≤n _ = func (𝑋-nattrans m≤n) ∘ (𝑋-type n) ⟪ m≤n , refl ⟫_
  morph-id 𝑋 {x = n} x =
    begin
      func (𝑋-nattrans {n} ≤-refl) (𝑋-type n ⟪ ≤-refl , refl ⟫ x)
    ≡⟨ eq (𝑋-nattrans-id {n}) _ ⟩
      𝑋-type n ⟪ ≤-refl , refl ⟫ x
    ≡⟨ morph-id (𝑋-type n) x ⟩
      x ∎
    where open ≡-Reasoning
  morph-comp 𝑋 {x = k}{y = m}{z = n} k≤m m≤n _ _ x =
    begin
      func (𝑋-nattrans (≤-trans k≤m m≤n)) (𝑋-type n ⟪ ≤-trans k≤m m≤n , refl ⟫ x)
    ≡⟨ eq (𝑋-nattrans-comp k≤m m≤n) _ ⟩
      func (𝑋-nattrans k≤m) (func (𝑋-nattrans m≤n) (𝑋-type n ⟪ ≤-trans k≤m m≤n , refl ⟫ x))
    ≡⟨ cong (func (𝑋-nattrans k≤m) ∘ func (𝑋-nattrans m≤n)) (morph-comp (𝑋-type n) k≤m m≤n refl refl x) ⟩
      func (𝑋-nattrans k≤m) (func (𝑋-nattrans m≤n) (𝑋-type n ⟪ k≤m , refl ⟫ (𝑋-type n ⟪ m≤n , refl ⟫ x)))
    ≡˘⟨ cong (func (𝑋-nattrans k≤m)) (naturality (𝑋-nattrans m≤n) _) ⟩
      func (𝑋-nattrans k≤m) (𝑋-type m ⟪ k≤m , refl ⟫ (func (𝑋-nattrans m≤n) (𝑋-type n ⟪ m≤n , refl ⟫ x))) ∎
    where open ≡-Reasoning

  fixpoint-from : F (▻' 𝑋) ↣ 𝑋
  func fixpoint-from {x = zero } fx = func strength g $⟨ ≤-refl , refl ⟩ fx
    where
      g : PresheafFunc 𝑋 Unit' zero _
      g $⟨ _ , _ ⟩ _ = tt
      naturality g _ _ _ = refl
  func fixpoint-from {x = suc n} fx = func strength g $⟨ ≤-refl , refl ⟩ fx
    where
      g : PresheafFunc 𝑋 (𝑋-type n) (suc n) _
      g $⟨ m≤n , _ ⟩ x = {!!}
      naturality g = {!!}
  naturality fixpoint-from = {!!}

  𝑋-fixpoint : F (▻' 𝑋) ≅ᵗʸ 𝑋
  from 𝑋-fixpoint = {!!}
  to 𝑋-fixpoint = {!!}
  isoˡ 𝑋-fixpoint = {!!}
  isoʳ 𝑋-fixpoint = {!!}
