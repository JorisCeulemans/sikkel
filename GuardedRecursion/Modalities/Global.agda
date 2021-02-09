--------------------------------------------------
-- The timeless-global dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.Global where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality hiding ([_]; setoid)

open import Categories
open import CwF-Structure

private
  variable
    ℓ ℓ' : Level
    Δ Γ Θ : Ctx ★ ℓ


timeless-ctx : Ctx ★ ℓ → Ctx ω ℓ
setoid (timeless-ctx Γ) _ = setoid Γ tt
rel (timeless-ctx Γ) _ γ = γ
rel-cong (timeless-ctx Γ) _ e = e
rel-id (timeless-ctx Γ) _ = ctx≈-refl Γ
rel-comp (timeless-ctx Γ) _ _ _ = ctx≈-refl Γ

timeless-subst : Δ ⇒ Γ → timeless-ctx Δ ⇒ timeless-ctx Γ
func (timeless-subst σ) = func σ
func-cong (timeless-subst σ) = func-cong σ
_⇒_.naturality (timeless-subst {Γ = Γ} σ) _ = ctx≈-refl Γ

timeless-subst-id : timeless-subst (id-subst Γ) ≅ˢ id-subst (timeless-ctx Γ)
eq (timeless-subst-id {Γ = Γ}) _ = ctx≈-refl Γ

timeless-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → timeless-subst (σ ⊚ τ) ≅ˢ timeless-subst σ ⊚ timeless-subst τ
eq (timeless-subst-⊚ {Θ = Θ} σ τ) _ = ctx≈-refl Θ

const-subst : Γ ⟨ tt ⟩ → ◇ ⇒ timeless-ctx Γ
func (const-subst γ) _ = γ
func-cong (const-subst {Γ = Γ} γ) _ = ctx≈-refl Γ
_⇒_.naturality (const-subst {Γ = Γ} γ) _ = ctx≈-refl Γ

const-subst-cong : {γ1 γ2 : Γ ⟨ tt ⟩} → γ1 ≈[ Γ ]≈ γ2 → const-subst {Γ = Γ} γ1 ≅ˢ const-subst γ2
eq (const-subst-cong eγ) tt = eγ

ty-const-subst-cong : {γ1 γ2 : Γ ⟨ tt ⟩} (T : Ty (timeless-ctx Γ) ℓ) →
                      γ1 ≈[ Γ ]≈ γ2 → T [ const-subst γ1 ] ≅ᵗʸ T [ const-subst γ2 ]
ty-const-subst-cong T eγ = ty-subst-cong-subst (const-subst-cong eγ) T

const-subst-natural : (δ : Δ ⟨ tt ⟩) (σ : Δ ⇒ Γ) → timeless-subst σ ⊚ const-subst δ ≅ˢ const-subst (func σ δ)
eq (const-subst-natural {Γ = Γ} δ σ) _ = ctx≈-refl Γ

tm-setoid : ∀ {C} (Γ : Ctx C ℓ) → Ty Γ ℓ' → Setoid (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
Setoid.Carrier (tm-setoid Γ T) = Tm Γ T
Setoid._≈_ (tm-setoid Γ T) = _≅ᵗᵐ_
Setoid.isEquivalence (tm-setoid Γ T) = record
  { refl = ≅ᵗᵐ-refl
  ; sym = ≅ᵗᵐ-sym
  ; trans = ≅ᵗᵐ-trans
  }

global-ty : Ty (timeless-ctx Γ) ℓ → Ty Γ ℓ
type (global-ty T) _ γ = tm-setoid ◇ (T [ const-subst γ ])
morph (global-ty {Γ = Γ} T) _ {γ}{γ'} eγ t = ι⁻¹[ ty-const-subst-cong T (ctx≈-trans Γ (ctx≈-sym Γ (rel-id Γ γ)) eγ) ] t
morph-cong (global-ty {Γ = Γ} T) _ {γy = γ} eγ = ι⁻¹-cong (ty-const-subst-cong T (ctx≈-trans Γ (ctx≈-sym Γ (rel-id Γ γ)) eγ))
morph-hom-cong (global-ty T) _ = record { eq = λ _ → morph-hom-cong T refl }
morph-id (global-ty T) _ = record { eq = λ _ → ty≈-trans T (morph-hom-cong T refl) (morph-id T _) }
morph-comp (global-ty T) _ _ _ _ _ =
  record { eq = λ _ → ty≈-trans T (morph-hom-cong T (≤-irrelevant _ _)) (morph-comp T ≤-refl ≤-refl _ _ _) }

module _ {T : Ty (timeless-ctx Γ) ℓ} where
  global-tm : Tm (timeless-ctx Γ) T → Tm Γ (global-ty T)
  term (term (global-tm t) tt γ) n tt = t ⟨ n , γ ⟩'
  Tm.naturality (term (global-tm t) tt γ) m≤n _ = Tm.naturality t m≤n _
  Tm.naturality (global-tm t) tt _ = record { eq = λ _ → Tm.naturality t ≤-refl _ }

  unglobal-tm : Tm Γ (global-ty T) → Tm (timeless-ctx Γ) T
  term (unglobal-tm t) n γ = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
  Tm.naturality (unglobal-tm t) {x = m}{y = n} m≤n {γy = γn}{γx = γm} eγ =
    begin
      T ⟪ m≤n , eγ ⟫ t ⟨ tt , γn ⟩' ⟨ n , tt ⟩'
    ≈˘⟨ morph-hom-cong-2-1 T (≤-irrelevant _ _) ⟩
      T ⟪ ≤-refl , _ ⟫ (T ⟪ m≤n , _ ⟫ t ⟨ tt , γn ⟩' ⟨ n , tt ⟩')
    ≈⟨ morph-cong T ≤-refl _ (Tm.naturality (t ⟨ tt , γn ⟩') m≤n refl) ⟩
      T ⟪ ≤-refl , _ ⟫ t ⟨ tt , γn ⟩' ⟨ m , tt ⟩'
    ≈⟨ eq (Tm.naturality t tt (ctx≈-trans Γ (rel-id Γ γn) eγ)) tt ⟩
      t ⟨ tt , γm ⟩' ⟨ m , tt ⟩' ∎
    where open SetoidReasoning (type T m γm)

  global-ty-β : (t : Tm (timeless-ctx Γ) T) → unglobal-tm (global-tm t) ≅ᵗᵐ t
  eq (global-ty-β t) _ = ty≈-refl T

  global-ty-η : (t : Tm Γ (global-ty T)) → global-tm (unglobal-tm t) ≅ᵗᵐ t
  eq (eq (global-ty-η t) γ) tt = ty≈-refl T

global-ty-cong : {T : Ty (timeless-ctx Γ) ℓ} {S : Ty (timeless-ctx Γ) ℓ'} →
                 T ≅ᵗʸ S → global-ty T ≅ᵗʸ global-ty S
func (from (global-ty-cong T=S)) = ι⁻¹[ ty-subst-cong-ty (const-subst _) T=S ]_
func-cong (from (global-ty-cong T=S)) = ι⁻¹-cong (ty-subst-cong-ty (const-subst _) T=S)
CwF-Structure.naturality (from (global-ty-cong T=S)) _ = record { eq = λ _ → CwF-Structure.naturality (from T=S) _ }
func (to (global-ty-cong T=S)) = ι[ ty-subst-cong-ty (const-subst _) T=S ]_
func-cong (to (global-ty-cong T=S)) = ι-cong (ty-subst-cong-ty (const-subst _) T=S)
CwF-Structure.naturality (to (global-ty-cong T=S)) _ = record { eq = λ _ → CwF-Structure.naturality (to T=S) _ }
eq (isoˡ (global-ty-cong T=S)) _ = ι-symʳ (ty-subst-cong-ty (const-subst _) T=S) _
eq (isoʳ (global-ty-cong T=S)) _ = ι-symˡ (ty-subst-cong-ty (const-subst _) T=S) _

ty-const-subst : (T : Ty (timeless-ctx Γ) ℓ) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                 (T [ timeless-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (timeless-subst σ) (const-subst _))
                                 (ty-subst-cong-subst (const-subst-natural _ σ) T)

global-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (timeless-ctx Γ) ℓ) → (global-ty T) [ σ ] ≅ᵗʸ global-ty (T [ timeless-subst σ ])
func (from (global-ty-natural σ T)) = ι[ ty-const-subst T σ _ ]_
func-cong (from (global-ty-natural σ T)) = ι-cong (ty-const-subst T σ _)
CwF-Structure.naturality (from (global-ty-natural σ T)) t = record { eq = λ _ → morph-hom-cong-2-2 T refl }
func (to (global-ty-natural σ T)) = ι⁻¹[ ty-const-subst T σ _ ]_
func-cong (to (global-ty-natural σ T)) = ι⁻¹-cong (ty-const-subst T σ _)
CwF-Structure.naturality (to (global-ty-natural σ T)) t = record { eq = λ _ → morph-hom-cong-2-2 T refl }
eq (isoˡ (global-ty-natural σ T)) t = ι-symˡ (ty-const-subst T σ _) t
eq (isoʳ (global-ty-natural σ T)) t = ι-symʳ (ty-const-subst T σ _) t

module _ (σ : Δ ⇒ Γ) {T : Ty (timeless-ctx Γ) ℓ} where
  global-tm-natural : (t : Tm (timeless-ctx Γ) T) →
                      (global-tm t) [ σ ]' ≅ᵗᵐ ι[ global-ty-natural σ T ] global-tm (t [ timeless-subst σ ]')
  eq (global-tm-natural t) _ = record { eq = λ _ → ty≈-trans T (ty≈-sym T (morph-id T _)) (morph-hom-cong T refl) }

  unglobal-tm-natural : (t : Tm Γ (global-ty T)) →
                        (unglobal-tm t) [ timeless-subst σ ]' ≅ᵗᵐ unglobal-tm (ι⁻¹[ global-ty-natural σ T ] (t [ σ ]'))
  eq (unglobal-tm-natural t) _ = ty≈-trans T (ty≈-sym T (morph-id T _)) (morph-hom-cong T refl)
