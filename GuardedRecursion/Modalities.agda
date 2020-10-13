module GuardedRecursion.Modalities where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality renaming (subst to transp) hiding ([_])

open import Categories
open import CwF-Structure

private
  variable
    ℓ ℓ' : Level
    Δ Γ Θ : Ctx ω ℓ

⨅ : Ctx ω ℓ → Ctx ★ ℓ
set (⨅ Γ) _ = Γ ⟨ 0 ⟩
rel (⨅ Γ) _ γ = γ
rel-id (⨅ Γ) _ = refl
rel-comp (⨅ Γ) _ _ _ = refl

⨅-subst : Δ ⇒ Γ → ⨅ Δ ⇒ ⨅ Γ
func (⨅-subst σ) = func σ
_⇒_.naturality (⨅-subst σ) _ = refl

⨅-subst-id : ⨅-subst (id-subst Γ) ≅ˢ id-subst (⨅ Γ)
eq ⨅-subst-id _ = refl

⨅-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → ⨅-subst (σ ⊚ τ) ≅ˢ ⨅-subst σ ⊚ ⨅-subst τ
eq (⨅-subst-⊚ σ τ) _ = refl

◬ : Ty (⨅ Γ) ℓ' → Ty Γ ℓ'
type (◬ {Γ = Γ} T) n γ = T ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩
morph (◬ {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ = T ⟪ tt , proof ⟫
  where
    open ≡-Reasoning
    proof : Γ ⟪ z≤n ⟫ γn ≡ Γ ⟪ z≤n ⟫ γm
    proof =
      begin
        Γ ⟪ z≤n ⟫ γn
      ≡⟨⟩
        Γ ⟪ ≤-trans z≤n m≤n ⟫ γn
      ≡⟨ rel-comp Γ z≤n m≤n γn ⟩
        Γ ⟪ z≤n ⟫ (Γ ⟪ m≤n ⟫ γn)
      ≡⟨ cong (Γ ⟪ z≤n ⟫_) eγ ⟩
        Γ ⟪ z≤n ⟫ γm ∎
morph-id (◬ T) t = trans (morph-cong T refl _ _) (morph-id T t)                       -- uip used here!
morph-comp (◬ T) _ _ _ _ t = trans (morph-cong T refl _ _) (morph-comp T tt tt _ _ t) -- uip used here!

module _ {T : Ty (⨅ Γ) ℓ} where
  ◬-intro : Tm (⨅ Γ) T → Tm Γ (◬ T)
  term (◬-intro t) n γ = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
  Tm.naturality (◬-intro t) _ _ = Tm.naturality t tt _

  ◬-elim : Tm Γ (◬ T) → Tm (⨅ Γ) T
  term (◬-elim t) _ γ = ctx-element-subst T (rel-id Γ γ) (t ⟨ 0 , γ ⟩')
  Tm.naturality (◬-elim t) _ eγ =
    begin
      T ⟪ tt , eγ ⟫ ctx-element-subst T (rel-id Γ _) (term t 0 _)
    ≡˘⟨ morph-comp T tt tt _ eγ (term t 0 _) ⟩
      T ⟪ tt , strong-rel-comp (⨅ Γ) (rel-id Γ _) eγ ⟫ (term t 0 _)
    ≡⟨ morph-cong T refl _ _ ⟩
      T ⟪ tt , _ ⟫ term t 0 _
    ≡⟨ morph-comp T tt tt _ _ _ ⟩
      ctx-element-subst T (rel-id Γ _) (T ⟪ tt , _ ⟫ (term t 0 _))
    ≡⟨ cong (ctx-element-subst T (rel-id Γ _)) (Tm.naturality t ≤-refl (trans (rel-id Γ _) eγ)) ⟩
      ctx-element-subst T (rel-id Γ _) (term t 0 _) ∎
    where open ≡-Reasoning

  ◬-intro-elim : (t : Tm Γ (◬ T)) → ◬-intro (◬-elim t) ≅ᵗᵐ t
  eq (◬-intro-elim t) γ =
    begin
      T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫ (t ⟨ 0 , Γ ⟪ z≤n ⟫ γ ⟩')
    ≡˘⟨ cong (T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫_) (Tm.naturality t z≤n refl) ⟩
      T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫ T ⟪ tt , _ ⟫ (t ⟨ _ , γ ⟩')
    ≡˘⟨ morph-comp T tt tt _ _ (term t _ γ) ⟩
      T ⟪ tt , _ ⟫ term t _ γ
    ≡⟨ morph-cong T refl _ _ ⟩
      T ⟪ _ , _ ⟫ term t _ γ
    ≡⟨ Tm.naturality t ≤-refl (rel-id Γ γ) ⟩
      t ⟨ _ , γ ⟩' ∎
    where open ≡-Reasoning

  ◬-elim-intro : (t : Tm (⨅ Γ) T) → ◬-elim (◬-intro t) ≅ᵗᵐ t
  eq (◬-elim-intro t) γ = Tm.naturality t tt _

◬-natural : (σ : Δ ⇒ Γ) (T : Ty (⨅ Γ) ℓ) → (◬ T) [ σ ] ≅ᵗʸ ◬ (T [ ⨅-subst σ ])
func (from (◬-natural σ T)) = ctx-element-subst T (_⇒_.naturality σ _)
CwF-Structure.naturality (from (◬-natural σ T)) t = {!!}
func (to (◬-natural σ T)) = ctx-element-subst T (sym (_⇒_.naturality σ _))
CwF-Structure.naturality (to (◬-natural σ T)) = {!!}
eq (isoˡ (◬-natural σ T)) t = {!!}
eq (isoʳ (◬-natural σ T)) t = {!!}

◬-intro-natural : (σ : Δ ⇒ Γ) {T : Ty (⨅ Γ) ℓ} (t : Tm (⨅ Γ) T) →
                  (◬-intro t) [ σ ]' ≅ᵗᵐ ι[ ◬-natural σ T ] ◬-intro (t [ ⨅-subst σ ]')
eq (◬-intro-natural σ t) = {!!}

◬-elim-natural : (σ : Δ ⇒ Γ) {T : Ty (⨅ Γ) ℓ} (t : Tm Γ (◬ T)) →
                 (◬-elim t) [ ⨅-subst σ ]' ≅ᵗᵐ ◬-elim (ι⁻¹[ ◬-natural σ T ] (t [ σ ]'))
eq (◬-elim-natural σ t) = {!!}
