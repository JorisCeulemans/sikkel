--------------------------------------------------
-- The now-timeless dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.Timeless where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality hiding ([_]; setoid)

open import Categories
open import CwF-Structure

private
  variable
    ℓ ℓ' r r' : Level
    Δ Γ Θ : Ctx ω ℓ r


now : Ctx ω ℓ r → Ctx ★ ℓ r
setoid (now Γ) _ = setoid Γ 0
rel (now Γ) _ γ = γ
rel-cong (now Γ) _ e = e
rel-id (now Γ) _ = ctx≈-refl Γ
rel-comp (now Γ) _ _ _ = ctx≈-refl Γ

now-subst : Δ ⇒ Γ → now Δ ⇒ now Γ
func (now-subst σ) = func σ
func-cong (now-subst σ) = func-cong σ
_⇒_.naturality (now-subst {Γ = Γ} σ) _ = ctx≈-refl Γ

now-subst-id : now-subst (id-subst Γ) ≅ˢ id-subst (now Γ)
eq (now-subst-id {Γ = Γ}) _ = ctx≈-refl Γ

now-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → now-subst (σ ⊚ τ) ≅ˢ now-subst σ ⊚ now-subst τ
eq (now-subst-⊚ {Θ = Θ} σ τ) _ = ctx≈-refl Θ

timeless-ty : Ty (now Γ) ℓ r → Ty Γ ℓ r
type (timeless-ty {Γ = Γ} T) n γ = type T tt (Γ ⟪ z≤n ⟫ γ)
morph (timeless-ty {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ  = T ⟪ tt , proof ⟫_
  where
    open SetoidReasoning (setoid Γ 0)
    proof : Γ ⟪ z≤n ⟫ γn ≈[ Γ ]≈ Γ ⟪ z≤n ⟫ γm
    proof =
      begin
        (Γ ⟪ z≤n ⟫ γn)
      ≈⟨ ctx≈-refl Γ ⟩
        (Γ ⟪ ≤-trans z≤n m≤n ⟫ γn)
      ≈⟨ rel-comp Γ z≤n m≤n γn ⟩
        Γ ⟪ z≤n ⟫ (Γ ⟪ m≤n ⟫ γn)
      ≈⟨ rel-cong Γ z≤n eγ ⟩
        Γ ⟪ z≤n ⟫ γm ∎
morph-cong (timeless-ty T) m≤n eγ = morph-cong T tt _
morph-hom-cong (timeless-ty T) e = morph-hom-cong T refl
morph-id (timeless-ty T) t = ty≈-trans T (morph-hom-cong T refl) (morph-id T t)
morph-comp (timeless-ty T) _ _ _ _ t = ty≈-trans T (morph-hom-cong T refl) (morph-comp T tt tt _ _ t)

module _ {T : Ty (now Γ) ℓ r} where
  timeless-tm : Tm (now Γ) T → Tm Γ (timeless-ty T)
  term (timeless-tm t) n γ = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
  Tm.naturality (timeless-tm t) _ _ = Tm.naturality t tt _

  untimeless-tm : Tm Γ (timeless-ty T) → Tm (now Γ) T
  term (untimeless-tm t) _ γ = ctx-element-subst T (rel-id Γ γ) (t ⟨ 0 , γ ⟩')
  Tm.naturality (untimeless-tm t) tt e = ty≈-trans T (morph-hom-cong-2-2 T refl)
                                                     (morph-cong T tt _ (Tm.naturality t z≤n (ctx≈-trans Γ (rel-id Γ _) e)))

  timeless-ty-η : (t : Tm Γ (timeless-ty T)) → timeless-tm (untimeless-tm t) ≅ᵗᵐ t
  eq (timeless-ty-η t) {n} γ =
    begin
      T ⟪ tt , _ ⟫ (t ⟨ 0 , Γ ⟪ z≤n ⟫ γ ⟩')
    ≈˘⟨ morph-cong T tt _ (Tm.naturality t z≤n (ctx≈-refl Γ)) ⟩
      T ⟪ tt , _ ⟫ T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≈⟨ morph-hom-cong-2-1 T refl ⟩
      T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≈⟨ Tm.naturality t ≤-refl (rel-id Γ γ) ⟩
      t ⟨ n , γ ⟩' ∎
    where open SetoidReasoning (type (timeless-ty T) n γ)

  timeless-ty-β : (t : Tm (now Γ) T) → untimeless-tm (timeless-tm t) ≅ᵗᵐ t
  eq (timeless-ty-β t) γ = Tm.naturality t tt _

timeless-ty-cong : {T : Ty (now Γ) ℓ r} {S : Ty (now Γ) ℓ' r'} → T ≅ᵗʸ S → timeless-ty T ≅ᵗʸ timeless-ty S
func (from (timeless-ty-cong T=S)) = func (from T=S)
func-cong (from (timeless-ty-cong T=S)) = func-cong (from T=S)
CwF-Structure.naturality (from (timeless-ty-cong T=S)) = CwF-Structure.naturality (from T=S)
func (to (timeless-ty-cong T=S)) = func (to T=S)
func-cong (to (timeless-ty-cong T=S)) = func-cong (to T=S)
CwF-Structure.naturality (to (timeless-ty-cong T=S)) = CwF-Structure.naturality (to T=S)
eq (isoˡ (timeless-ty-cong T=S)) = eq (isoˡ T=S)
eq (isoʳ (timeless-ty-cong T=S)) = eq (isoʳ T=S)

module _ {T : Ty (now Γ) ℓ r} where
  timeless-tm-cong : {t s : Tm (now Γ) T} → t ≅ᵗᵐ s → timeless-tm t ≅ᵗᵐ timeless-tm s
  eq (timeless-tm-cong t=s) γ = eq t=s (Γ ⟪ z≤n ⟫ γ)

  untimeless-tm-cong : {t s : Tm Γ (timeless-ty T)} → t ≅ᵗᵐ s → untimeless-tm t ≅ᵗᵐ untimeless-tm s
  eq (untimeless-tm-cong t=s) γ = morph-cong T tt _ (eq t=s γ)

timeless-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (now Γ) ℓ r) → (timeless-ty T) [ σ ] ≅ᵗʸ timeless-ty (T [ now-subst σ ])
func (from (timeless-ty-natural σ T)) = ctx-element-subst T (_⇒_.naturality σ _)
func-cong (from (timeless-ty-natural σ T)) = morph-cong T tt _
CwF-Structure.naturality (from (timeless-ty-natural σ T)) t = morph-hom-cong-2-2 T refl
func (to (timeless-ty-natural {Γ = Γ} σ T)) = ctx-element-subst T (ctx≈-sym Γ (_⇒_.naturality σ _))
func-cong (to (timeless-ty-natural σ T)) = morph-cong T tt _
CwF-Structure.naturality (to (timeless-ty-natural σ T)) t = morph-hom-cong-2-2 T refl
eq (isoˡ (timeless-ty-natural σ T)) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _ ⟫ t)
  ≈⟨ morph-hom-cong-2-1 T refl ⟩
    T ⟪ tt , _ ⟫ t
  ≈⟨ morph-id T t ⟩
    t ∎
  where open SetoidReasoning (type T tt _)
eq (isoʳ (timeless-ty-natural σ T)) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _ ⟫ t)
  ≈⟨ morph-hom-cong-2-1 T refl ⟩
    T ⟪ tt , _ ⟫ t
  ≈⟨ morph-id T t ⟩
    t ∎
  where open SetoidReasoning (type T tt _)

module _ (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ r} where
  timeless-tm-natural : (t : Tm (now Γ) T) →
                        (timeless-tm t) [ σ ]' ≅ᵗᵐ ι[ timeless-ty-natural σ T ] timeless-tm (t [ now-subst σ ]')
  eq (timeless-tm-natural t) δ = ty≈-sym T (Tm.naturality t tt _)

  untimeless-tm-natural : (t : Tm Γ (timeless-ty T)) →
                          (untimeless-tm t) [ now-subst σ ]' ≅ᵗᵐ untimeless-tm (ι⁻¹[ timeless-ty-natural σ T ] (t [ σ ]'))
  eq (untimeless-tm-natural t) δ = ty≈-sym T (morph-hom-cong-2-1 T refl)
