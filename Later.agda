module Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure
open import Types.Functions

--------------------------------------------------
-- Later modality for types
--------------------------------------------------

ctx-m≤1+n : (Γ : Ctx ℓ) (m≤n : m ≤ n) (γ : Γ ⟨ suc n ⟩) →
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n Γ m≤n γ = trans (cong-app (sym (rel-comp Γ m≤n (n≤1+n _))) γ)
                          (trans (cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _))
                                 (cong-app (rel-comp Γ (n≤1+n _) (s≤s m≤n)) γ))

▻ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
type (▻ {Γ = Γ} T) zero _ = Lift _ ⊤
type (▻ {Γ = Γ} T) (suc n) γ = T ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩
morph (▻ {Γ = Γ} T) z≤n γ = λ _ → lift tt
morph (▻ {Γ = Γ} T) (s≤s ineq) γ t = subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ ineq γ) (T ⟪ ineq , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)
morph-id (▻ {Γ = Γ} T) {zero} γ = refl
morph-id (▻ {Γ = Γ} T) {suc n} γ = funext λ t →
  subst (λ x → T ⟨ n , Γ ⟪ n≤1+n n ⟫ (x γ) ⟩) (rel-id Γ)
    (subst (λ x → T ⟨ n , x ⟩) (ctx-m≤1+n Γ ≤-refl γ) (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t))
      ≡⟨ subst-∘ (rel-id Γ) ⟩
  subst (λ x → T ⟨ n , x ⟩) (cong (λ z → Γ ⟪ n≤1+n n ⟫ (z γ)) (rel-id Γ))
    (subst (λ x → T ⟨ n , x ⟩) (ctx-m≤1+n Γ ≤-refl γ) (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t))
      ≡⟨ subst-subst (ctx-m≤1+n Γ ≤-refl γ) ⟩
  subst (λ x → T ⟨ n , x ⟩) (trans (ctx-m≤1+n Γ ≤-refl γ) (cong (λ z → Γ ⟪ n≤1+n n ⟫ (z γ)) (rel-id Γ)))
    (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t)
      ≡⟨ cong (λ z → subst (λ x → T ⟨ n , x ⟩) z
                            (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t))
              (uip _ _) ⟩
  subst (λ x → T ⟨ n , x ⟩) (cong-app (rel-id Γ) (Γ ⟪ n≤1+n n ⟫ γ))
    (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t)
      ≡⟨ subst-cong-app (rel-id Γ) _ ⟩
  subst (λ x → T ⟨ n , x (Γ ⟪ n≤1+n n ⟫ γ) ⟩) (rel-id Γ)
    (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t)
      ≡⟨ cong-app (morph-id T (Γ ⟪ n≤1+n n ⟫ γ)) t ⟩
  t ∎
  where open ≡-Reasoning
morph-comp (▻ T) z≤n m≤n γ = refl
morph-comp (▻ {Γ = Γ} T) (s≤s k≤m) (s≤s m≤n) γ = funext λ t →
  subst (λ x → T ⟨ _ , Γ ⟪ n≤1+n _ ⟫ (x γ) ⟩) (rel-comp Γ (s≤s k≤m) (s≤s m≤n))
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ (≤-trans k≤m m≤n) γ) (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
      ≡⟨ subst-∘ (rel-comp Γ (s≤s k≤m) (s≤s m≤n)) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (cong (λ z → Γ ⟪ n≤1+n _ ⟫ (z γ)) (rel-comp Γ (s≤s k≤m) (s≤s m≤n)))
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ (≤-trans k≤m m≤n) γ) (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
      ≡⟨ subst-subst (ctx-m≤1+n Γ (≤-trans k≤m m≤n) γ) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (trans (ctx-m≤1+n Γ (≤-trans k≤m m≤n) γ)
                                   (cong (λ z → Γ ⟪ n≤1+n _ ⟫ (z γ)) (rel-comp Γ (s≤s k≤m) (s≤s m≤n))))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)
      ≡⟨ cong (λ z → subst (λ x → T ⟨ _ , x ⟩) z
                            (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
              (uip _ _) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (trans (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
                                   (trans (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n Γ m≤n γ))
                                          (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)
      ≡⟨ sym (subst-subst (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (trans (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n Γ m≤n γ))
                                          (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ)))
    (subst (λ x → T ⟨ _ , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
      ≡⟨ sym (subst-subst (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n Γ m≤n γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n Γ m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ)))
              (sym (subst-∘ (ctx-m≤1+n Γ m≤n γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n Γ m≤n γ)
    (subst (λ x → T ⟨ _ , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (λ z → subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
                            (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n Γ m≤n γ) z))
              (subst-cong-app (rel-comp Γ k≤m m≤n) _) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n Γ m≤n γ)
    (subst (λ x → T ⟨ _ , x (Γ ⟪ n≤1+n _ ⟫ γ) ⟩) (rel-comp Γ k≤m m≤n)
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (λ z → subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
                            (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n Γ m≤n γ) z))
              (cong-app (morph-comp T k≤m m≤n (Γ ⟪ n≤1+n _ ⟫ γ)) t) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n Γ m≤n γ)
    (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n _ ⟫ γ) ⟫
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ)))
              (weak-subst-application (λ x → T ⟪ k≤m , x ⟫) (ctx-m≤1+n Γ m≤n γ)) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (T ⟪ k≤m , Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ s≤s m≤n ⟫ γ) ⟫
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n Γ m≤n γ)
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))) ∎
  where open ≡-Reasoning

next : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm Γ (▻ T)
term (next {Γ = Γ} t) = λ { zero γ → lift tt ; (suc n) γ → t ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩' }
naturality (next t) = λ ineq γ → {!!}
