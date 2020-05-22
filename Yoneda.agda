module Yoneda where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts

-- Yoneda embedding
𝕪 : ℕ → Ctx ℓ
set (𝕪 n) m = Lift _ (m ≤ n)
rel (𝕪 n) k≤m (lift m≤n) = lift (≤-trans k≤m m≤n)
rel-id (𝕪 n) (lift _) = cong lift (≤-irrelevant _ _)
rel-comp (𝕪 n) _ _ (lift _) = cong lift (≤-irrelevant _ _)

𝕪[_]_ : ∀ ℓ → ℕ → Ctx ℓ
𝕪[ ℓ ] n = 𝕪 {ℓ} n

-- The Yoneda lemma
to-𝕪⇒* : {Γ : Ctx ℓ} {n : ℕ} → Γ ⟨ n ⟩ → 𝕪 n ⇒ Γ
func (to-𝕪⇒* {Γ = Γ} γ) (lift ineq) = Γ ⟪ ineq ⟫ γ
naturality (to-𝕪⇒* {Γ = Γ} γ) (lift ineq) = sym (rel-comp Γ _ ineq γ)

from-𝕪⇒* : {Γ : Ctx ℓ} {n : ℕ} → 𝕪 n ⇒ Γ → Γ ⟨ n ⟩
from-𝕪⇒* σ = func σ (lift ≤-refl)

𝕪-to-∘-from : {Γ : Ctx ℓ} {n : ℕ} (σ : 𝕪 n ⇒ Γ) → to-𝕪⇒* (from-𝕪⇒* σ) ≅ˢ σ
eq (𝕪-to-∘-from σ) (lift ineq) = trans (naturality σ (lift ≤-refl))
                                       (cong (func σ ∘ lift) (≤-irrelevant _ _))

𝕪-from-∘-to : {Γ : Ctx ℓ} {n : ℕ} (γ : Γ ⟨ n ⟩) → from-𝕪⇒* {Γ = Γ} (to-𝕪⇒* γ) ≡ γ
𝕪-from-∘-to {Γ = Γ} γ = rel-id Γ γ

-- Proving that the Yoneda embedding is fully faithful
to-𝕪⇒𝕪 : m ≤ n → 𝕪[ ℓ ] m ⇒ 𝕪 n
to-𝕪⇒𝕪 = to-𝕪⇒* ∘ lift

from-𝕪⇒𝕪 : 𝕪[ ℓ ] m ⇒ 𝕪 n → m ≤ n
from-𝕪⇒𝕪 = lower ∘ from-𝕪⇒*

𝕪-from-∘-to' : (ineq : m ≤ n) → from-𝕪⇒𝕪 (to-𝕪⇒𝕪 {ℓ = ℓ} ineq) ≡ ineq
𝕪-from-∘-to' ineq = ≤-irrelevant _ _

𝕪-to-∘-from' : (σ : 𝕪[ ℓ ] m ⇒ 𝕪 n) → to-𝕪⇒𝕪 (from-𝕪⇒𝕪 σ) ≅ˢ σ
𝕪-to-∘-from' σ = 𝕪-to-∘-from σ

𝕪-refl : to-𝕪⇒𝕪 (≤-refl {m}) ≅ˢ id-subst (𝕪[ ℓ ] m)
eq 𝕪-refl (lift ineq) = cong lift (≤-irrelevant _ _)

𝕪-comp : {Γ : Ctx ℓ} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → to-𝕪⇒* {Γ = Γ} γ ⊚ to-𝕪⇒𝕪 ineq ≅ˢ to-𝕪⇒* (Γ ⟪ ineq ⟫ γ)
eq (𝕪-comp {Γ = Γ} ineq γ) (lift ineq') = rel-comp Γ ineq' ineq γ
