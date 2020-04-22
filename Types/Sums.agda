module Types.Sums where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

--------------------------------------------------
-- Sum types
--------------------------------------------------

_⊞_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ⊞ S) n γ = T ⟨ n , γ ⟩ ⊎ S ⟨ n , γ ⟩
morph (T ⊞ S) m≤n eq (inl t) = inl (T ⟪ m≤n , eq ⟫ t)
morph (T ⊞ S) m≤n eq (inr s) = inr (S ⟪ m≤n , eq ⟫ s)
morph-id (T ⊞ S) (inl t) = cong inl (morph-id T t)
morph-id (T ⊞ S) (inr s) = cong inr (morph-id S s)
morph-comp (T ⊞ S) k≤m m≤n eq-nm eq-mk (inl t) = cong inl (morph-comp T k≤m m≤n eq-nm eq-mk t)
morph-comp (T ⊞ S) k≤m m≤n eq-nm eq-mk (inr s) = cong inr (morph-comp S k≤m m≤n eq-nm eq-mk s)

module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  inl' : Tm Γ T → Tm Γ (T ⊞ S)
  term (inl' t) n γ = inl (t ⟨ n , γ ⟩')
  naturality (inl' t) m≤n eq = cong inl (naturality t m≤n eq)

  inr' : Tm Γ S → Tm Γ (T ⊞ S)
  term (inr' s) n γ = inr (s ⟨ n , γ ⟩')
  naturality (inr' s) m≤n eq = cong inr (naturality s m≤n eq)

inl'⟨_⟩_ : {Γ : Ctx ℓ} {T : Ty Γ} (S : Ty Γ) (t : Tm Γ T) → Tm Γ (T ⊞ S)
inl'⟨ S ⟩ t = inl' {S = S} t

inr'⟨_⟩_ : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} (s : Tm Γ S) → Tm Γ (T ⊞ S)
inr'⟨ T ⟩ s = inr' {T = T} s

module _ {Δ Γ : Ctx ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊞-natural : (T ⊞ S) [ σ ] ≡ (T [ σ ]) ⊞ (S [ σ ])
  ⊞-natural = cong₃-d (MkTy _)
                        (funextI (funextI (funext λ m≤n → funextI (funextI (funext λ eq → funext λ {
                          (inl t) → refl ;
                          (inr s) → refl })))))
                        (funextI (funextI (funext λ _ → uip _ _)))
                        (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

  inl'-natural : (t : Tm Γ T) → subst (Tm Δ) ⊞-natural ((inl' t) [ σ ]') ≡ inl' (t [ σ ]')
  inl'-natural t = cong₂-d MkTm
    (term (subst (Tm Δ) ⊞-natural (inl' t [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ⊞-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ⊞-natural (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨ subst-∘ ⊞-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ⊞-natural) (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))) {x = cong type ⊞-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ⊞ S) [ σ ])} refl (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨⟩
      term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funextI (funextI (funext λ _ → uip _ _)))))
    where open ≡-Reasoning

  inr'-natural : (s : Tm Γ S) → subst (Tm Δ) ⊞-natural ((inr' s) [ σ ]') ≡ inr' (s [ σ ]')
  inr'-natural s = cong₂-d MkTm
    (term (subst (Tm Δ) ⊞-natural (inr' s [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ⊞-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ⊞-natural (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨ subst-∘ ⊞-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ⊞-natural) (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))) {x = cong type ⊞-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ⊞ S) [ σ ])} refl (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨⟩
      term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funextI (funextI (funext λ _ → uip _ _)))))
    where open ≡-Reasoning
