module Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure

--------------------------------------------------
-- Later modality for types
--------------------------------------------------

▻ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
type (▻ {Γ = Γ} T) = λ { zero _ → Lift _ ⊤ ; (suc n) γ → T ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩ }
morph (▻ {Γ = Γ} T) = λ { z≤n γ → λ _ → lift tt ; (s≤s ineq) γ t →
                        subst (λ x → T ⟨ _ , x ⟩)
                              (Γ ⟪ ineq ⟫ (Γ ⟪ n≤1+n _ ⟫ γ)
                                  ≡⟨ cong-app (sym (rel-comp Γ _ _)) γ ⟩
                                Γ ⟪ ≤-trans ineq (n≤1+n _) ⟫ γ
                                  ≡⟨ cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _) ⟩
                                Γ ⟪ ≤-trans (n≤1+n _) (s≤s ineq) ⟫ γ
                                  ≡⟨ cong-app (rel-comp Γ _ _) γ ⟩
                                Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ s≤s ineq ⟫ γ) ∎)
                              (T ⟪ ineq , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t) }
  where open ≡-Reasoning
morph-id (▻ T) {zero} γ = refl
morph-id (▻ T) {suc n} γ = {!!}
morph-comp (▻ T) = {!!}

next : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm Γ (▻ T)
term (next {Γ = Γ} t) = λ { zero γ → lift tt ; (suc n) γ → t ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩' }
naturality (next t) = λ ineq γ → {!!}
