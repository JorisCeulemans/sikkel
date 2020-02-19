module Yoneda where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure

-- Yoneda embedding
𝕪 : ℕ → Ctx ℓ
𝕪 n = record { set = λ m → Lift _ (m ≤ n)
             ; rel = λ { k≤m (lift m≤n) → lift (≤-trans k≤m m≤n) }
             ; rel-id = funext λ { (lift _) → cong lift (≤-irrelevant _ _) }
             ; rel-comp = λ _ _ → funext λ { (lift _) → cong lift (≤-irrelevant _ _) }
             }
{-
set (𝕪 n) = λ m → Lift _ (m ≤ n)
rel (𝕪 n) = λ { k≤m (lift m≤n) → lift (≤-trans k≤m m≤n) }
rel-id (𝕪 n) = funext λ { (lift _) → cong lift (≤-irrelevant _ _) }
rel-comp (𝕪 n) = λ _ _ → funext λ { (lift _) → cong lift (≤-irrelevant _ _) }
-}

𝕪[_]_ : ∀ ℓ → ℕ → Ctx ℓ
𝕪[ ℓ ] n = 𝕪 {ℓ} n

-- The Yonede lemma
to-𝕪⇒* : {Γ : Ctx ℓ} (n : ℕ) → Γ ⟨ n ⟩ → 𝕪 n ⇒ Γ
func (to-𝕪⇒* {Γ = Γ} n γ) (lift ineq) = Γ ⟪ ineq ⟫ γ
naturality (to-𝕪⇒* {Γ = Γ} n γ) = funext (λ { (lift ineq) → cong-app (sym (rel-comp Γ _ ineq)) γ })

from-𝕪⇒* : {Γ : Ctx ℓ} (n : ℕ) → 𝕪 n ⇒ Γ → Γ ⟨ n ⟩
from-𝕪⇒* n σ = func σ (lift ≤-refl)

𝕪-to-∘-from : {Γ : Ctx ℓ} (n : ℕ) (σ : 𝕪 n ⇒ Γ) → to-𝕪⇒* n (from-𝕪⇒* n σ) ≡ σ
𝕪-to-∘-from n σ = cong₂-d MkSubst (funextI (funext λ { (lift ineq) → trans (cong-app (naturality σ) (lift ≤-refl))
                                                                            (cong (func σ ∘ lift) (≤-irrelevant _ _)) }))
                                  (funextI (funextI (funextI (uip _ _))))

𝕪-from-∘-to : {Γ : Ctx ℓ} (n : ℕ) (γ : Γ ⟨ n ⟩) → from-𝕪⇒* {Γ = Γ} n (to-𝕪⇒* n γ) ≡ γ
𝕪-from-∘-to {Γ = Γ} n γ = cong-app (rel-id Γ) γ

-- Proving that the Yoneda embedding is fully faithful
to-𝕪⇒𝕪 : m ≤ n → 𝕪[ ℓ ] m ⇒ 𝕪 n
to-𝕪⇒𝕪 = to-𝕪⇒* _ ∘ lift

from-𝕪⇒𝕪 : 𝕪[ ℓ ] m ⇒ 𝕪 n → m ≤ n
from-𝕪⇒𝕪 = lower ∘ from-𝕪⇒* _
