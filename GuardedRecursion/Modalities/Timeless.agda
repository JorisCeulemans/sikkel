--------------------------------------------------
-- The now-timeless dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.Timeless where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure

private
  variable
    ℓ ℓ' : Level
    Δ Γ Θ : Ctx ω ℓ


now : Ctx ω ℓ → Ctx ★ ℓ
set (now Γ) _ = Γ ⟨ 0 ⟩
rel (now Γ) _ γ = γ
rel-id (now Γ) _ = refl
rel-comp (now Γ) _ _ _ = refl

now-subst : Δ ⇒ Γ → now Δ ⇒ now Γ
func (now-subst σ) = func σ
_⇒_.naturality (now-subst σ) _ = refl

now-subst-id : now-subst (id-subst Γ) ≅ˢ id-subst (now Γ)
eq now-subst-id _ = refl

now-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → now-subst (σ ⊚ τ) ≅ˢ now-subst σ ⊚ now-subst τ
eq (now-subst-⊚ σ τ) _ = refl

timeless-ty : Ty (now Γ) ℓ' → Ty Γ ℓ'
type (timeless-ty {Γ = Γ} T) n γ = T ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩
morph (timeless-ty {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ = T ⟪ tt , proof ⟫
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
morph-cong (timeless-ty T) e = morph-cong T refl
morph-id (timeless-ty T) t = trans (morph-cong T refl) (morph-id T t)
morph-comp (timeless-ty T) _ _ _ _ t = trans (morph-cong T refl) (morph-comp T tt tt _ _ t)

module _ {T : Ty (now Γ) ℓ} where
  timeless-tm : Tm (now Γ) T → Tm Γ (timeless-ty T)
  term (timeless-tm t) n γ = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
  Tm.naturality (timeless-tm t) _ _ = Tm.naturality t tt _

  untimeless-tm : Tm Γ (timeless-ty T) → Tm (now Γ) T
  term (untimeless-tm t) _ γ = ctx-element-subst T (rel-id Γ γ) (t ⟨ 0 , γ ⟩')
  Tm.naturality (untimeless-tm t) tt refl = morph-id T _

  timeless-ty-η : (t : Tm Γ (timeless-ty T)) → timeless-tm (untimeless-tm t) ≅ᵗᵐ t
  eq (timeless-ty-η t) {n} γ =
    begin
      T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫ (t ⟨ 0 , Γ ⟪ z≤n ⟫ γ ⟩')
    ≡˘⟨ cong (T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫_) (Tm.naturality t z≤n refl) ⟩
      T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫ T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡˘⟨ morph-comp T tt tt _ _ (t ⟨ n , γ ⟩') ⟩
      T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ Tm.naturality t ≤-refl (rel-id Γ γ) ⟩
      t ⟨ n , γ ⟩' ∎
    where open ≡-Reasoning

  timeless-ty-β : (t : Tm (now Γ) T) → untimeless-tm (timeless-tm t) ≅ᵗᵐ t
  eq (timeless-ty-β t) γ = Tm.naturality t tt _

timeless-ty-cong : {T : Ty (now Γ) ℓ} {S : Ty (now Γ) ℓ'} → T ≅ᵗʸ S → timeless-ty T ≅ᵗʸ timeless-ty S
func (from (timeless-ty-cong T=S)) = func (from T=S)
CwF-Structure.naturality (from (timeless-ty-cong T=S)) = CwF-Structure.naturality (from T=S)
func (to (timeless-ty-cong T=S)) = func (to T=S)
CwF-Structure.naturality (to (timeless-ty-cong T=S)) = CwF-Structure.naturality (to T=S)
eq (isoˡ (timeless-ty-cong T=S)) = eq (isoˡ T=S)
eq (isoʳ (timeless-ty-cong T=S)) = eq (isoʳ T=S)

-- TODO: Show that timeless-tm and untimeless-tm are congruent as well.

timeless-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (now Γ) ℓ) → (timeless-ty T) [ σ ] ≅ᵗʸ timeless-ty (T [ now-subst σ ])
func (from (timeless-ty-natural σ T)) = ctx-element-subst T (_⇒_.naturality σ _)
CwF-Structure.naturality (from (timeless-ty-natural σ T)) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
  ≡˘⟨ morph-comp T tt tt _ _ t ⟩
    T ⟪ tt , _ ⟫ t
  ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
    T ⟪ tt , _ ⟫ t
  ≡⟨ morph-comp T tt tt _ _ t ⟩
    T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , _ ⟫ t) ∎
  where open ≡-Reasoning
func (to (timeless-ty-natural σ T)) = ctx-element-subst T (sym (_⇒_.naturality σ _))
CwF-Structure.naturality (to (timeless-ty-natural σ T)) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
  ≡˘⟨ morph-comp T tt tt _ _ t ⟩
    T ⟪ tt , _ ⟫ t
  ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
    T ⟪ tt , _ ⟫ t
  ≡⟨ morph-comp T tt tt _ _ t ⟩
    T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _ ⟫ t) ∎
  where open ≡-Reasoning
eq (isoˡ (timeless-ty-natural σ T)) t =
  begin
    T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
  ≡˘⟨ morph-comp T tt tt _ _ t ⟩
    T ⟪ tt , _ ⟫ t
  ≡⟨ morph-cong T refl ⟩
    T ⟪ tt , refl ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (timeless-ty-natural σ T)) t =
  begin
    T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
  ≡˘⟨ morph-comp T tt tt _ _ t ⟩
    T ⟪ tt , _ ⟫ t
  ≡⟨ morph-cong T refl ⟩
    T ⟪ tt , refl ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
  where open ≡-Reasoning

timeless-tm-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ} (t : Tm (now Γ) T) →
                  (timeless-tm t) [ σ ]' ≅ᵗᵐ ι[ timeless-ty-natural σ T ] timeless-tm (t [ now-subst σ ]')
eq (timeless-tm-natural σ t) δ = sym (Tm.naturality t tt _)

untimeless-tm-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ} (t : Tm Γ (timeless-ty T)) →
                 (untimeless-tm t) [ now-subst σ ]' ≅ᵗᵐ untimeless-tm (ι⁻¹[ timeless-ty-natural σ T ] (t [ σ ]'))
eq (untimeless-tm-natural {Δ = Δ}{Γ = Γ} σ {T = T} t) δ =
  begin
    T ⟪ tt , rel-id Γ (func σ δ) ⟫ (t ⟨ 0 , func σ δ ⟩')
  ≡⟨ morph-cong T refl ⟩
    T ⟪ tt , _ ⟫ (t ⟨ 0 , func σ δ ⟩')
  ≡⟨ morph-comp T tt tt _ _ _ ⟩
    T ⟪ tt , cong (func σ) (rel-id Δ δ) ⟫ (T ⟪ tt , _⇒_.naturality σ δ ⟫ (t ⟨ 0 , func σ δ ⟩')) ∎
  where open ≡-Reasoning
