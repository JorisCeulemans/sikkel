module CwF-Structure.Terms where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types

--------------------------------------------------
-- Terms
--------------------------------------------------

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  constructor MkTm
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (term n γ) ≡ term m (Γ ⟪ ineq ⟫ γ)
open Tm public

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ

_⟪_,_⟫' : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (t ⟨ n , γ ⟩') ≡ t ⟨ m , Γ ⟪ ineq ⟫ γ ⟩'
t ⟪ ineq , γ ⟫' = naturality t ineq γ

_[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
term (t [ σ ]') = λ n δ → t ⟨ n , func σ δ ⟩'
naturality (_[_]'  {Δ = Δ}{Γ}{T} t σ) ineq δ = 
  (T [ σ ]) ⟪ ineq , δ ⟫ (t [ σ ]' ⟨ _ , δ ⟩')
    ≡⟨⟩
  subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ineq , func σ δ ⟫ (t ⟨ _ , func σ δ ⟩'))
    ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)) (t ⟪ ineq , func σ δ ⟫') ⟩
  subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (t ⟨ _ , Γ ⟪ ineq ⟫ (func σ δ) ⟩')
    ≡⟨ cong-d (λ x → t ⟨ _ , x ⟩') (naturality σ δ) ⟩
  t ⟨ _ , func σ (Δ ⟪ ineq ⟫ δ) ⟩'
    ≡⟨⟩
  t [ σ ]' ⟨ _ , Δ ⟪ ineq ⟫ δ ⟩' ∎
  where open ≡-Reasoning

tm-subst-id : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]') ≡ t
tm-subst-id {Γ = Γ}{T = T} t = cong₂-d MkTm
  (term (subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]'))
      ≡⟨ sym (weak-subst-application {B = Tm Γ} (λ x y → term y) (ty-subst-id T)) ⟩
    subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x ⟨ n , γ ⟩) (ty-subst-id T) (term (t [ id-subst Γ ]'))
      ≡⟨ subst-∘ (ty-subst-id T) ⟩
    subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) (cong type (ty-subst-id T)) (term (t [ id-subst Γ ]'))
      ≡⟨ cong {A = type T ≡ type T} (λ y → subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) y (term t)) (uip _ _) ⟩
    subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) {x = type T} refl (term t)
      ≡⟨⟩
    term t ∎)
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
  where open ≡-Reasoning

tm-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]') ≡ t [ τ ⊚ σ ]'
tm-subst-comp {Δ = Δ}{Γ}{T = T} t τ σ = cong₂-d MkTm
  (term (subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]'))
      ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) (ty-subst-comp T τ σ)) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x ⟨ n , δ ⟩) (ty-subst-comp T τ σ) (term (t [ τ ]' [ σ ]'))
      ≡⟨ subst-∘ (ty-subst-comp T τ σ) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) (cong type (ty-subst-comp T τ σ)) (term (t [ τ ]' [ σ ]'))
      ≡⟨ cong {A = (λ n δ → type T n (func τ (func σ δ))) ≡ (λ n δ → type T n (func τ (func σ δ)))}
              (λ y → subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) y (term (t [ τ ]' [ σ ]')))
              {x = cong type (ty-subst-comp T τ σ)}
              {y = refl}
              (uip _ _) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) {x = type (T [ τ ⊚ σ ])} refl (term (t [ τ ⊚ σ ]'))
      ≡⟨⟩
    term (t [ τ ⊚ σ ]') ∎)
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
  where open ≡-Reasoning
