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

subst-⊎ˡ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
           {x x' : A} (e : x ≡ x') {y : B x} →
           subst (λ x → B x ⊎ C x) e (inl y) ≡ inl (subst B e y)
subst-⊎ˡ e = weak-subst-application (λ _ w → inl w) e

subst-⊎ʳ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
           {x x' : A} (e : x ≡ x') {z : C x} →
           subst (λ x → B x ⊎ C x) e (inr z) ≡ inr (subst C e z)
subst-⊎ʳ e = weak-subst-application (λ _ w → inr w) e

_⊎'_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
_⊎'_ {Γ = Γ} T S = MkTy (λ n γ → T ⟨ n , γ ⟩ ⊎ S ⟨ n , γ ⟩)
                         (λ { ineq γ (inl t) → inl (T ⟪ ineq , γ ⟫ t) ; ineq γ (inr s) → inr (S ⟪ ineq , γ ⟫ s) })
                         (λ { (inl t) → trans (subst-⊎ˡ _) (cong inl (morph-id T t))
                            ; (inr s) → trans (subst-⊎ʳ _) (cong inr (morph-id S s)) })
                         (λ k≤m m≤n → λ { (inl t) → trans (subst-⊎ˡ _) (cong inl (morph-comp T k≤m m≤n t))
                                         ; (inr s) → trans (subst-⊎ʳ _) (cong inr (morph-comp S k≤m m≤n s)) })
{-
type (T ⊎' S) = λ n γ → T ⟨ n , γ ⟩ ⊎ S ⟨ n , γ ⟩
morph (T ⊎' S) = λ { ineq γ (inl t) → inl (T ⟪ ineq , γ ⟫ t) ; ineq γ (inr s) → inr (S ⟪ ineq , γ ⟫ s) }
morph-id (T ⊎' S) = λ γ → funext λ { (inl t) → {!trans ? ?!} ; (inr s) → {!!} }
morph-comp (T ⊎' S) = {!!}
-}

module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  inl' : Tm Γ T → Tm Γ (T ⊎' S)
  term (inl' t) = λ n γ → inl (t ⟨ n , γ ⟩')
  naturality (inl' t) = λ ineq γ → cong inl (t ⟪ ineq , γ ⟫')

  inr' : Tm Γ S → Tm Γ (T ⊎' S)
  term (inr' s) = λ n γ → inr (s ⟨ n , γ ⟩')
  naturality (inr' s) = λ ineq γ → cong inr (s ⟪ ineq , γ ⟫')

inl'⟨_⟩_ : {Γ : Ctx ℓ} {T : Ty Γ} (S : Ty Γ) (t : Tm Γ T) → Tm Γ (T ⊎' S)
inl'⟨ S ⟩ t = inl' {S = S} t

inr'⟨_⟩_ : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} (s : Tm Γ S) → Tm Γ (T ⊎' S)
inr'⟨ T ⟩ s = inr' {T = T} s

module _ {Δ Γ : Ctx ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
  abstract
    ⊎'-natural : (T ⊎' S) [ σ ] ≡ (T [ σ ]) ⊎' (S [ σ ])
    ⊎'-natural = cong₃-d (MkTy _)
                          (funextI (funextI (funext λ ineq → funext λ δ → funext λ {
                            (inl t) → subst-⊎ˡ (naturality σ δ) ;
                            (inr s) → subst-⊎ʳ (naturality σ δ) })))
                          (funextI (funextI (funext λ _ → uip _ _)))
                          (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))

  inl'-natural : (t : Tm Γ T) → subst (Tm Δ) ⊎'-natural ((inl' t) [ σ ]') ≡ inl' (t [ σ ]')
  inl'-natural t = cong₂-d MkTm
    (term (subst (Tm Δ) ⊎'-natural (inl' t [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ⊎'-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ⊎'-natural (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨ subst-∘ ⊎'-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ⊎'-natural) (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))) {x = cong type ⊎'-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ⊎' S) [ σ ])} refl (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨⟩
      term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

  inr'-natural : (s : Tm Γ S) → subst (Tm Δ) ⊎'-natural ((inr' s) [ σ ]') ≡ inr' (s [ σ ]')
  inr'-natural s = cong₂-d MkTm
    (term (subst (Tm Δ) ⊎'-natural (inr' s [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ⊎'-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ⊎'-natural (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨ subst-∘ ⊎'-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ⊎'-natural) (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))) {x = cong type ⊎'-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ⊎' S) [ σ ])} refl (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨⟩
      term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning
