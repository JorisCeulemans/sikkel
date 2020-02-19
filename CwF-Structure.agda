module CwF-Structure where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers

infixl 15 _,,_
infix 10 _⇒_
infix 15 _⟨_,_⟩
infixl 20 _⊚_

--------------------------------------------------
-- Contexts and substitutions + category structure
--------------------------------------------------

record Ctx ℓ : Set (lsuc ℓ) where
  field
    set : ℕ → Set ℓ
    rel : ∀ {m n} → m ≤ n → set n → set m
    rel-id : ∀ {n} → rel {n} (≤-refl) ≡ id
    rel-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) → rel (≤-trans k≤m m≤n) ≡ rel k≤m ∘ rel m≤n
open Ctx public

_⟨_⟩ : Ctx ℓ → ℕ → Set ℓ
Γ ⟨ n ⟩ = set Γ n

_⟪_⟫ : (Γ : Ctx ℓ) (ineq : m ≤ n) → Γ ⟨ n ⟩ → Γ ⟨ m ⟩
Γ ⟪ ineq ⟫ = rel Γ ineq

_⟪_⟫_ : (Γ : Ctx ℓ) (ineq : m ≤ n) → Γ ⟨ n ⟩ → Γ ⟨ m ⟩
Γ ⟪ ineq ⟫ γ = (Γ ⟪ ineq ⟫) γ

-- The empty context
◇ : Ctx ℓ
set ◇ = λ _ → Lift _ ⊤
rel ◇ = λ _ _ → lift tt
rel-id ◇ = refl
rel-comp ◇ = λ _ _ → refl

-- Yoneda embedding
𝕪 : ℕ → Ctx 0ℓ
set (𝕪 n) = λ m → m ≤ n
rel (𝕪 n) = ≤-trans
rel-id (𝕪 n) = funext (λ _ → ≤-irrelevant _ _)
rel-comp (𝕪 n) = λ m1≤m2 m2≤m3 → funext (λ _ → ≤-irrelevant _ _)

record _⇒_ {ℓ} (Δ Γ : Ctx ℓ) : Set ℓ where
  constructor MkSubst
  field
    func : ∀ {n} → Δ ⟨ n ⟩ → Γ ⟨ n ⟩
    naturality : ∀ {m n ineq} → (Γ ⟪ ineq ⟫) ∘ func {n} ≡ func {m} ∘ (Δ ⟪ ineq ⟫)
open _⇒_ public

id-subst : (Γ : Ctx ℓ) → Γ ⇒ Γ
func (id-subst Γ) = id
naturality (id-subst Γ) = refl

_⊚_ : {Δ Γ Θ : Ctx ℓ} → Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
func (τ ⊚ σ) = func τ ∘ func σ
naturality (_⊚_ {Δ = Δ}{Γ}{Θ} τ σ) {ineq = ineq} =
  Θ ⟪ ineq ⟫ ∘ func τ ∘ func σ ≡⟨ cong (_∘ func σ) (naturality τ) ⟩
  func τ ∘ Γ ⟪ ineq ⟫ ∘ func σ ≡⟨ cong (func τ ∘_) (naturality σ) ⟩
  func τ ∘ func σ ∘ Δ ⟪ ineq ⟫ ∎
  where open ≡-Reasoning

⊚-id-substʳ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≡ σ
⊚-id-substʳ σ = cong (MkSubst _) (funextI (funextI (funextI (trans (trans-reflʳ _) (cong-id _)))))

⊚-id-substˡ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≡ σ
⊚-id-substˡ σ = cong (MkSubst _) (funextI (funextI (funextI (trans (trans-reflʳ _) (cong-id _)))))

⊚-assoc : {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx ℓ} (σ₃₄ : Γ₃ ⇒ Γ₄) (σ₂₃ : Γ₂ ⇒ Γ₃) (σ₁₂ : Γ₁ ⇒ Γ₂) → σ₃₄ ⊚ σ₂₃ ⊚ σ₁₂ ≡ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
⊚-assoc σ₃₄ σ₂₃ σ₁₂ = cong (MkSubst _) (funextI (funextI (funextI (uip _ _))))
{-
  naturality (σ₃₄ ⊚ σ₂₃ ⊚ σ₁₂)
    ≡⟨⟩
  trans (cong (_∘ func σ₁₂) (trans (cong (_∘ func σ₂₃) (naturality σ₃₄))
                                   (trans (cong (func σ₃₄ ∘_) (naturality σ₂₃)) refl)))
        (trans (cong ((func σ₃₄ ∘ func σ₂₃) ∘_) (naturality σ₁₂)) refl)
    ≡⟨ cong (λ x → trans (cong (_∘ func σ₁₂) (trans (cong (_∘ func σ₂₃) (naturality σ₃₄))
                                              (trans (cong (func σ₃₄ ∘_) (naturality σ₂₃)) refl)))
                          (trans x refl)) (cong-∘ _) ⟩
  trans (cong (_∘ func σ₁₂) (trans (cong (_∘ func σ₂₃) (naturality σ₃₄))
                                   (trans (cong (func σ₃₄ ∘_) (naturality σ₂₃)) refl)))
        (trans (cong (func σ₃₄ ∘_) (cong (func σ₂₃ ∘_) (naturality σ₁₂))) refl)
    ≡⟨ {!!} ⟩
  trans (cong (_∘ func σ₁₂) (cong (_∘ func σ₂₃) (naturality σ₃₄)))
        (trans (cong (func σ₃₄ ∘_) (trans (cong (_∘ func σ₁₂) (naturality σ₂₃))
                                          (trans (cong (func σ₂₃ ∘_) (naturality σ₁₂)) refl)))
               refl)
    ≡⟨ cong (λ x → trans x (trans (cong (func σ₃₄ ∘_) (trans (cong (_∘ func σ₁₂) (naturality σ₂₃))
                                                           (trans (cong (func σ₂₃ ∘_) (naturality σ₁₂)) refl)))
                                   refl)) (sym (cong-∘ (naturality σ₃₄))) ⟩
  trans (cong (_∘ (func σ₂₃ ∘ func σ₁₂)) (naturality σ₃₄))
        (trans (cong (func σ₃₄ ∘_) (trans (cong (_∘ func σ₁₂) (naturality σ₂₃))
                                          (trans (cong (func σ₂₃ ∘_) (naturality σ₁₂)) refl)))
               refl)
    ≡⟨⟩
  naturality (σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)) ∎))))
  where open ≡-Reasoning
-}

empty-subst : (Γ : Ctx ℓ) → Γ ⇒ ◇
func (empty-subst Γ) = λ _ → lift tt
naturality (empty-subst Γ) = refl

empty-subst-terminal : (Γ : Ctx ℓ) (σ : Γ ⇒ ◇) → σ ≡ empty-subst Γ
empty-subst-terminal Γ σ = cong (MkSubst _) (funextI (funextI (funextI λ {_} → to-⊤-hset _ _)))


--------------------------------------------------
-- Types
--------------------------------------------------

record Ty {ℓ} (Γ : Ctx ℓ) : Set (lsuc ℓ) where
  constructor MkTy
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) → type n γ → type m (Γ ⟪ m≤n ⟫ γ)
    morph-id : ∀ {n} (γ : Γ ⟨ n ⟩) → subst (λ x → type n (x γ)) (rel-id Γ {n}) ∘ morph ≤-refl γ ≡ id
    morph-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) →
                 subst (λ x → type k (x γ)) (rel-comp Γ k≤m m≤n) ∘ morph (≤-trans k≤m m≤n) γ ≡ morph k≤m (Γ ⟪ m≤n ⟫ γ) ∘ morph m≤n γ
open Ty public

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ = morph T ineq γ

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ t = (T ⟪ ineq , γ ⟫) t

morph-id-app : {Γ : Ctx ℓ} (T : Ty Γ) (γ : Γ ⟨ n ⟩) (t : T ⟨ n , γ ⟩) →
               subst (λ x → T ⟨ n , x ⟩) (cong-app (rel-id Γ) γ) (T ⟪ ≤-refl , γ ⟫ t) ≡ t
morph-id-app {Γ = Γ} T γ t = trans (subst-cong-app (rel-id Γ) (T ⟪ ≤-refl , γ ⟫ t)) (cong-app (morph-id T γ) t)

morph-comp-app : {Γ : Ctx ℓ} (T : Ty Γ) {k≤m : k ≤ m} {m≤n : m ≤ n} (γ : Γ ⟨ n ⟩) (t : T ⟨ n , γ ⟩) →
                 subst (λ x → T ⟨ k , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) γ) (T ⟪ ≤-trans k≤m m≤n , γ ⟫ t) ≡ T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ (T ⟪ m≤n , γ ⟫ t)
morph-comp-app {Γ = Γ} T {k≤m}{m≤n} γ t = trans (subst-cong-app (rel-comp Γ k≤m m≤n) _) (cong-app (morph-comp T k≤m m≤n γ) t)

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) = λ n δ → T ⟨ n , func σ δ ⟩
morph (T [ σ ]) ineq δ t = subst (λ x → T ⟨ _ , x δ ⟩) (naturality σ {ineq = ineq}) (T ⟪ ineq , func σ δ ⟫ t)
morph-id (_[_] {Δ = Δ}{Γ} T σ) δ = proof
  where
     open ≡-Reasoning
     abstract
       proof = funext (λ t →
         subst (λ x → T ⟨ _ , func σ (x δ) ⟩) (rel-id Δ) (subst (λ x → T ⟨ _ , x δ ⟩) (naturality σ) (T ⟪ ≤-refl , func σ δ ⟫ t))
           ≡⟨ subst-∘ (rel-id Δ) ⟩
         subst (λ x → T ⟨ _ , x δ ⟩) (cong (func σ ∘_) (rel-id Δ)) (subst (λ x → T ⟨ _ , x δ ⟩) (naturality σ) (T ⟪ ≤-refl , func σ δ ⟫ t))
           ≡⟨ subst-subst (naturality σ) ⟩
         subst (λ x → T ⟨ _ , x δ ⟩) (trans (naturality σ) (cong (func σ ∘_) (rel-id Δ))) (T ⟪ ≤-refl , func σ δ ⟫ t)
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x δ ⟩) y (T ⟪ ≤-refl , func σ δ ⟫ t)) (uip _ (cong (_∘ func σ) (rel-id Γ))) ⟩
             -- Currently this equality is proven using uip. In a setting without uip, we would need to impose an extra coherence requirement
             -- on substitutions, ensuring that trans (naturality σ) (cong (func σ ∘_) (rel-id Δ)) ≡ cong (_∘ func σ) (rel-id Γ).
         subst (λ x → T ⟨ _ , x δ ⟩) (cong (_∘ func σ) (rel-id Γ)) (T ⟪ ≤-refl , func σ δ ⟫ t)
           ≡⟨ sym (subst-∘ (rel-id Γ)) ⟩
         subst (λ x → T ⟨ _ , x (func σ δ) ⟩) (rel-id Γ) (T ⟪ ≤-refl , func σ δ ⟫ t)
           ≡⟨ cong-app (morph-id T (func σ δ)) t ⟩
         t ∎)
morph-comp (_[_] {Δ = Δ}{Γ} T σ) k≤m m≤n δ = proof
  where
     open ≡-Reasoning
     abstract
       proof = funext (λ t →
         subst (λ x → T ⟨ _ , func σ (x δ) ⟩) (rel-comp Δ k≤m m≤n)
           (subst (λ x → T ⟨ _ , x δ ⟩) (naturality σ)
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ subst-∘ (rel-comp Δ k≤m m≤n) ⟩
         subst (λ x → T ⟨ _ , x δ ⟩) (cong (func σ ∘_) (rel-comp Δ k≤m m≤n))
           (subst (λ x → T ⟨ _ , x δ ⟩) (naturality σ)
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ subst-subst (naturality σ) ⟩
         subst (λ x → T ⟨ _ , x δ ⟩)
           (trans (naturality σ) (cong (func σ ∘_) (rel-comp Δ k≤m m≤n)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x δ ⟩) y (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
                   (uip (trans (naturality σ) (cong (func σ ∘_) (rel-comp Δ k≤m m≤n))) _) ⟩
           -- Again, without uip we would need to include an extra coherence law for substitutions.
         subst (λ x → T ⟨ _ , x δ ⟩)
           (trans (trans (cong (_∘ func σ) (rel-comp Γ k≤m m≤n)) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ))) (cong (_∘ Δ ⟪ m≤n ⟫) (naturality σ)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
           ≡⟨ sym (subst-subst (trans (cong (_∘ func σ) (rel-comp Γ k≤m m≤n)) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ)))) ⟩
         subst (λ x → T ⟨ _ , x δ ⟩) (cong (_∘ Δ ⟪ m≤n ⟫) (naturality σ))
           (subst (λ x → T ⟨ _ , x δ ⟩) (trans (cong (_∘ func σ) (rel-comp Γ k≤m m≤n)) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ sym (subst-∘ (naturality σ)) ⟩
         subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)
           (subst (λ x → T ⟨ _ , x δ ⟩) (trans (cong (_∘ func σ) (rel-comp Γ k≤m m≤n)) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ cong (subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)) (sym (subst-subst (cong (_∘ func σ) (rel-comp Γ k≤m m≤n)))) ⟩
         subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)
           (subst (λ x → T ⟨ _ , x δ ⟩) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ))
             (subst (λ x → T ⟨ _ , x δ ⟩) (cong (_∘ func σ) (rel-comp Γ k≤m m≤n))
               (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ) (subst (λ x → T ⟨ _ , x δ ⟩) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ)) y))
                   (sym (subst-∘ (rel-comp Γ k≤m m≤n))) ⟩
         subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)
           (subst (λ x → T ⟨ _ , x δ ⟩) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ))
             (subst (λ x → T ⟨ _ , x (func σ δ) ⟩) (rel-comp Γ k≤m m≤n)
               (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ) (subst (λ x → T ⟨ _ , x δ ⟩) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ)) y))
                   (cong-app (morph-comp T k≤m m≤n (func σ δ)) t) ⟩
         subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)
           (subst (λ x → T ⟨ _ , x δ ⟩) (cong (Γ ⟪ k≤m ⟫ ∘_) (naturality σ))
             (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)) (sym (subst-∘ (naturality σ))) ⟩
         subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)
           (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ (x δ) ⟩) (naturality σ)
             (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ))
                   (weak-subst-application (λ x y → T ⟪ k≤m , x δ ⟫ y) (naturality σ)) ⟩
         subst (λ x → T ⟨ _ , x (Δ ⟪ m≤n ⟫ δ) ⟩) (naturality σ)
           (T ⟪ k≤m , func σ (Δ ⟪ m≤n ⟫ δ) ⟫
             (subst (λ x → T ⟨ _ , x δ ⟩) (naturality σ) (T ⟪ m≤n , func σ δ ⟫ t))) ∎)

abstract
  ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
  ty-subst-id T = cong₂-d (MkTy _ _)
                          (funextI (funext λ _ → uip _ _))
                          (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _))))

  ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
  ty-subst-comp T τ σ = cong₃-d (MkTy _)
    (funextI (funextI (funext λ ineq → funext λ δ → funext λ t →
        subst (λ x → T ⟨ _ , func τ (x δ) ⟩) (naturality σ)
        (subst (λ x → T ⟨ _ , x (func σ δ) ⟩) (naturality τ)
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ subst-∘ (naturality σ)  ⟩
        subst (λ x → T ⟨ _ , x δ ⟩) (cong (func τ ∘_) (naturality σ))
        (subst (λ x → T ⟨ _ , x (func σ δ) ⟩) (naturality τ)
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ cong (subst (λ x → T ⟨ _  , x δ ⟩) (cong (func τ ∘_) (naturality σ))) (subst-∘ (naturality τ)) ⟩
        subst (λ x → T ⟨ _ , x δ ⟩) (cong (func τ ∘_) (naturality σ))
        (subst (λ x → T ⟨ _ , x δ ⟩) (cong (_∘ func σ) (naturality τ))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ subst-subst (cong (_∘ func σ) (naturality τ))  ⟩
        subst (λ x → T ⟨ _ , x δ ⟩)
          (trans (cong (_∘ func σ) (naturality τ)) (cong (func τ ∘_) (naturality σ)))
          (T ⟪ ineq , func τ (func σ δ) ⟫ t)
         ≡⟨ cong
              (λ p →
                 subst (λ x → T ⟨ _ , x δ ⟩) p
                 (T ⟪ ineq , func τ (func σ δ) ⟫ t))
              (cong (trans (cong (_∘ func σ) (naturality τ))) (sym (trans-reflʳ (cong (func τ ∘_) (naturality σ))))) ⟩
         subst (λ x → T ⟨ _ , x δ ⟩)
           (trans (cong (_∘ func σ) (naturality τ))
             (trans (cong (func τ ∘_) (naturality σ))
           refl))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t) ∎
        )))
    (funextI (funext (λ _ → uip _ _)))
    (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _))))
    where open ≡-Reasoning


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
  subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq}) (T ⟪ ineq , func σ δ ⟫ (t ⟨ _ , func σ δ ⟩'))
    ≡⟨ cong (subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq})) (t ⟪ ineq , func σ δ ⟫') ⟩
  subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq}) (t ⟨ _ , Γ ⟪ ineq ⟫ (func σ δ) ⟩')
    ≡⟨ cong-d (λ x → t ⟨ _ , x δ ⟩') (naturality σ) ⟩
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

_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
Γ ,, T = record { set = λ n → Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
                ; rel = λ { ineq [ γ , t ] → [ Γ ⟪ ineq ⟫ γ , T ⟪ ineq , γ ⟫ t ] }
                ; rel-id = funext λ { [ γ , t ] → to-Σ-eq (cong-app (rel-id Γ) γ) (morph-id-app T γ t) }
                ; rel-comp = λ k≤m m≤n → funext λ { [ γ , t ] → to-Σ-eq (cong-app (rel-comp Γ k≤m m≤n) γ) (morph-comp-app T γ t) }
                }
{- Same definition using copattern matching (currently fails, but will probably work in Agda 2.6.1).
set (Γ ,, T) n = Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) ineq [ γ , t ] = [ Γ ⟪ ineq ⟫ γ , T ⟪ ineq , γ ⟫ t ]
rel-id (Γ ,, T) = funext λ { [ γ , t ] → to-Σ-eq (cong-app (rel-id Γ) γ) (trans {!!} (cong-app (morph-id T γ) t)) }
rel-comp (Γ ,, T) = λ k≤m m≤n → funext λ { [ γ , t ] → {!to-Σ-eq ? ?!} }
  -- Strange behaviour here (termination checking seems to fail).
  -- It is possible that this will be solved by https://github.com/agda/agda/pull/4424 in Agda 2.6.1.
-}
π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π = refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π {T = T} ])
term ξ = λ _ → proj₂
naturality ξ = λ _ _ → refl

ctx-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))
ctx-ext-subst {Δ = Δ}{Γ}{T} τ = [ π {T = T} ⊚ τ , subst (Tm Δ) (ty-subst-comp T (π {T = T}) τ) (ξ {T = T} [ τ ]') ]

ctx-ext-subst⁻¹ : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ])) → Δ ⇒ Γ ,, T
func (ctx-ext-subst⁻¹ [ σ , t ]) = λ δ → [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (ctx-ext-subst⁻¹ [ σ , t ]) = funext (λ δ → to-Σ-eq (cong-app (naturality σ) δ)
                                                                (trans (subst-cong-app (naturality σ) _)
                                                                       (naturality t _ δ)))
