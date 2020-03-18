module Types.Products where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

--------------------------------------------------
-- (Non-dependent) product types
--------------------------------------------------

subst-× : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
          {x x' : A} (e : x ≡ x')
          (p : B x × C x) →
          subst (λ x → B x × C x) e p ≡ [ subst B e (proj₁ p) , subst C e (proj₂ p) ]
subst-× refl p = refl

_×'_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
_×'_ {Γ = Γ} T S = MkTy (λ n γ → T ⟨ n , γ ⟩ × S ⟨ n , γ ⟩)
                   (λ { ineq γ [ t , s ] → [ T ⟪ ineq , γ ⟫ t , S ⟪ ineq , γ ⟫ s ] })
                   (λ { [ t , s ] → trans (subst-× (rel-id Γ _) _)
                                                         (cong₂ [_,_] (morph-id T t)
                                                                      (morph-id S s)) })
                   (λ k≤m m≤n → λ { [ t , s ] → trans (subst-× (rel-comp Γ k≤m m≤n _) _)
                                                                 (cong₂ [_,_] (morph-comp T k≤m m≤n t)
                                                                              (morph-comp S k≤m m≤n s)) })

module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  pair : Tm Γ T → Tm Γ S → Tm Γ (T ×' S)
  term (pair t s) = λ n γ → [ t ⟨ n , γ ⟩' , s ⟨ n , γ ⟩' ]
  naturality (pair t s) = λ ineq γ → cong₂ [_,_] (t ⟪ ineq , γ ⟫') (s ⟪ ineq , γ ⟫')

  fst : Tm Γ (T ×' S) → Tm Γ T
  term (fst p) = λ n γ → proj₁ (p ⟨ n , γ ⟩')
  naturality (fst p) = λ ineq γ → cong proj₁ (p ⟪ _ , γ ⟫')

  snd : Tm Γ (T ×' S) → Tm Γ S
  term (snd p) = λ n γ → proj₂ (p ⟨ n , γ ⟩')
  naturality (snd p) = λ ineq γ → cong proj₂ (p ⟪ _ , γ ⟫')

module _ {Δ Γ : Ctx ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
--  abstract
  ×'-natural : (T ×' S) [ σ ] ≡ (T [ σ ]) ×' (S [ σ ])
  ×'-natural = cong₃-d (MkTy _)
                       (funextI (funextI (funext λ ineq → funext λ δ → funext λ { [ t , s ] →
                         subst-× (naturality σ δ) [ T ⟪ ineq , func σ δ ⟫ t , S ⟪ ineq , func σ δ ⟫ s ] })))
                       (funextI (funextI (funext λ _ → uip _ _)))
                       (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))

  pair-natural : (t : Tm Γ T) (s : Tm Γ S) → subst (Tm Δ) ×'-natural ((pair t s) [ σ ]') ≡ pair (t [ σ ]') (s [ σ ]')
  pair-natural t s = cong₂-d MkTm
    (term (subst (Tm Δ) ×'-natural (pair t s [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ×'-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ×'-natural (term (pair t s [ σ ]'))
        ≡⟨ subst-∘ ×'-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ×'-natural) (term (pair t s [ σ ]'))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (pair t s [ σ ]'))) {x = cong type ×'-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ×' S) [ σ ])} refl (term (pair (t [ σ ]') (s [ σ ]')))
        ≡⟨⟩
      term (pair (t [ σ ]') (s [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

  fst-natural : (p : Tm Γ (T ×' S)) → (fst p) [ σ ]' ≡ fst (subst (Tm Δ) ×'-natural (p [ σ ]'))
  fst-natural p = cong₂-d MkTm
    (term (fst p [ σ ]')
        ≡⟨ cong (λ z → λ n δ → proj₁ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) z (term (p [ σ ]')) n δ)) {x = refl} {y = cong type ×'-natural} (uip _ _) ⟩
      (λ n δ → proj₁ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) (cong type ×'-natural) (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₁ (z n δ)) (sym (subst-∘ {P = λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ} {f = type} ×'-natural)) ⟩
      (λ n δ → proj₁ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z ⟨ n₁ , γ ⟩) ×'-natural (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₁ (z n δ)) (weak-subst-application {B = Tm Δ} (λ x y → term y) ×'-natural) ⟩
      term (fst (subst (Tm Δ) ×'-natural (p [ σ ]'))) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

  snd-natural : (p : Tm Γ (T ×' S)) → (snd p) [ σ ]' ≡ snd (subst (Tm Δ) ×'-natural (p [ σ ]'))
  snd-natural p = cong₂-d MkTm
    (term (snd p [ σ ]')
        ≡⟨ cong (λ z → λ n δ → proj₂ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) z (term (p [ σ ]')) n δ)) {x = refl} {y = cong type ×'-natural} (uip _ _) ⟩
      (λ n δ → proj₂ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) (cong type ×'-natural) (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₂ (z n δ)) (sym (subst-∘ {P = λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ} {f = type} ×'-natural)) ⟩
      (λ n δ → proj₂ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z ⟨ n₁ , γ ⟩) ×'-natural (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₂ (z n δ)) (weak-subst-application {B = Tm Δ} (λ x y → term y) ×'-natural) ⟩
      term (snd (subst (Tm Δ) ×'-natural (p [ σ ]'))) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

β-×-fst : {Γ : Ctx ℓ} {T S : Ty Γ} (t : Tm Γ T) (s : Tm Γ S) →
          fst (pair t s) ≡ t
β-×-fst t s = cong₂-d MkTm refl (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))

β-×-snd : {Γ : Ctx ℓ} {T S : Ty Γ} (t : Tm Γ T) (s : Tm Γ S) →
          snd (pair t s) ≡ s
β-×-snd t s = cong₂-d MkTm refl (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))

η-× : {Γ : Ctx ℓ} {T S : Ty Γ} (p : Tm Γ (T ×' S)) →
      p ≡ pair (fst p) (snd p)
η-× p = cong₂-d MkTm refl (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
