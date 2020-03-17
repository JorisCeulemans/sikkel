module CwF-Structure.Types where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts

infix 15 _⟨_,_⟩
infixr 11 _⟪_,_⟫_

--------------------------------------------------
-- Types
--------------------------------------------------

record Ty {ℓ} (Γ : Ctx ℓ) : Set (lsuc ℓ) where
  constructor MkTy
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) → type n γ → type m (Γ ⟪ m≤n ⟫ γ)
    morph-id : ∀ {n} {γ : Γ ⟨ n ⟩} (t : type n γ) →
               subst (λ x → type n x) (rel-id Γ γ) (morph ≤-refl γ t) ≡ t
    morph-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) {γ : Γ ⟨ n ⟩} (t : type n γ) →
                 subst (λ x → type k x) (rel-comp Γ k≤m m≤n γ) (morph (≤-trans k≤m m≤n) γ t) ≡ morph k≤m (Γ ⟪ m≤n ⟫ γ) (morph m≤n γ t)
open Ty public

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ = morph T ineq γ

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ t = (T ⟪ ineq , γ ⟫) t

{- TODO: see if it is a good idea using the following way to prove equality of types
   + uniform way to prove type equality
   - using funext to show that type T ≡ type S where refl can be used most of the time
to-ty-eq : {Γ : Ctx ℓ} {T S : Ty Γ} →
           (et : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ ≡ S ⟨ n , γ ⟩) →
           ({m n : ℕ} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) (t : T ⟨ n , γ ⟩) →
               subst id (et m (Γ ⟪ m≤n ⟫ γ)) (T ⟪ m≤n , γ ⟫ t) ≡ S ⟪ m≤n , γ ⟫ subst id (et n γ) t) →
           T ≡ S
to-ty-eq et em = cong₄-d MkTy
                         (funext λ n → funext λ γ → et n γ)
                         {!!}
                         {!!}
                         {!!}
-}

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) = λ n δ → T ⟨ n , func σ δ ⟩
morph (T [ σ ]) m≤n δ t = subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ m≤n , func σ δ ⟫ t)
morph-id (_[_] {Δ = Δ}{Γ} T σ) {n} {δ} t = proof
  where
     open ≡-Reasoning
--     abstract
     proof =
       subst (λ x → T ⟨ _ , func σ x ⟩) (rel-id Δ δ) (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ≤-refl , func σ δ ⟫ t))
         ≡⟨ subst-∘ (rel-id Δ δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (cong (func σ) (rel-id Δ δ)) (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ≤-refl , func σ δ ⟫ t))
         ≡⟨ subst-subst (naturality σ δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (trans (naturality σ δ) (cong (func σ) (rel-id Δ δ))) (T ⟪ ≤-refl , func σ δ ⟫ t)
         ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) y (T ⟪ ≤-refl , func σ δ ⟫ t)) (uip _ (rel-id Γ (func σ δ))) ⟩
           -- Currently this equality is proven using uip. In a setting without uip, we would need to impose an extra coherence requirement
           -- on substitutions, ensuring that trans (naturality σ) (cong (func σ ∘_) (rel-id Δ)) ≡ cong (_∘ func σ) (rel-id Γ).
       subst (λ x → T ⟨ _ , x ⟩) (rel-id Γ (func σ δ)) (T ⟪ ≤-refl , func σ δ ⟫ t)
         ≡⟨ morph-id T t ⟩
       t ∎
morph-comp (_[_] {Δ = Δ}{Γ} T σ) k≤m m≤n {δ} t = proof
  where
     open ≡-Reasoning
--     abstract
     proof =
       subst (λ x → T ⟨ _ , func σ x ⟩) (rel-comp Δ k≤m m≤n δ)
         (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
         ≡⟨ subst-∘ (rel-comp Δ k≤m m≤n δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (cong (func σ) (rel-comp Δ k≤m m≤n δ))
         (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
         ≡⟨ subst-subst (naturality σ δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩)
         (trans (naturality σ δ) (cong (func σ) (rel-comp Δ k≤m m≤n δ)))
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
         ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) y (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
                 (uip (trans (naturality σ δ) (cong (func σ) (rel-comp Δ k≤m m≤n δ))) _) ⟩
         -- Again, without uip we would need to include an extra coherence law for substitutions.
       subst (λ x → T ⟨ _ , x ⟩)
         (trans (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))) (naturality σ (Δ ⟪ m≤n ⟫ δ)))
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
         ≡⟨ sym (subst-subst (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)))) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , x ⟩) (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)))
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
         ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))) (sym (subst-subst (rel-comp Γ k≤m m≤n (func σ δ)))) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))
           (subst (λ x → T ⟨ _ , x ⟩) (rel-comp Γ k≤m m≤n (func σ δ))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)))
         ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ)) (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)) y))
                 (morph-comp T k≤m m≤n t) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))
           (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
         ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))) (sym (subst-∘ (naturality σ δ))) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (naturality σ δ)
           (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
         ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ)))
                 (weak-subst-application (λ x y → T ⟪ k≤m , x ⟫ y) (naturality σ δ)) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (T ⟪ k≤m , func σ (Δ ⟪ m≤n ⟫ δ) ⟫
           (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ m≤n , func σ δ ⟫ t))) ∎

abstract
  ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
  ty-subst-id T = cong₂-d (MkTy _ _)
                          (funextI (funextI (funext (λ _ → uip _ _))))
                          (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))

  ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
  ty-subst-comp T τ σ = cong₃-d (MkTy _)
    (funextI (funextI (funext λ ineq → funext λ δ → funext λ t →
        subst (λ x → T ⟨ _ , func τ x ⟩) (naturality σ δ)
        (subst (λ x → T ⟨ _ , x ⟩) (naturality τ (func σ δ))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ subst-∘ (naturality σ δ)  ⟩
        subst (λ x → T ⟨ _ , x ⟩) (cong (func τ) (naturality σ δ))
        (subst (λ x → T ⟨ _ , x ⟩) (naturality τ (func σ δ))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ subst-subst (naturality τ (func σ δ))  ⟩
        subst (λ x → T ⟨ _ , x ⟩)
          (trans (naturality τ (func σ δ)) (cong (func τ) (naturality σ δ)))
          (T ⟪ ineq , func τ (func σ δ) ⟫ t)
         ≡⟨ cong
              (λ p →
                 subst (λ x → T ⟨ _ , x ⟩) p
                 (T ⟪ ineq , func τ (func σ δ) ⟫ t))
              (cong (trans (naturality τ (func σ δ))) (sym (trans-reflʳ _))) ⟩
         subst (λ x → T ⟨ _ , x ⟩)
           (trans (naturality τ (func σ δ))
             (trans (cong (func τ) (naturality σ δ))
           refl))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t) ∎
        )))
    (funextI (funextI (funext (λ _ → uip _ _))))
    (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))
    where open ≡-Reasoning
