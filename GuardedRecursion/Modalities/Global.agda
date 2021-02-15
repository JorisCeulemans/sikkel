--------------------------------------------------
-- The timeless-global dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.Global where

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
    Δ Γ Θ : Ctx ★


timeless-ctx : Ctx ★ → Ctx ω
set (timeless-ctx Γ) _ = Γ ⟨ tt ⟩
rel (timeless-ctx Γ) _ γ = γ
rel-id (timeless-ctx Γ) _ = refl
rel-comp (timeless-ctx Γ) _ _ _ = refl

timeless-subst : Δ ⇒ Γ → timeless-ctx Δ ⇒ timeless-ctx Γ
func (timeless-subst σ) = func σ
_⇒_.naturality (timeless-subst σ) _ = refl

timeless-subst-id : timeless-subst (id-subst Γ) ≅ˢ id-subst (timeless-ctx Γ)
eq timeless-subst-id _ = refl

timeless-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → timeless-subst (σ ⊚ τ) ≅ˢ timeless-subst σ ⊚ timeless-subst τ
eq (timeless-subst-⊚ σ τ) _ = refl

const-subst : Γ ⟨ tt ⟩ → ◇ ⇒ timeless-ctx Γ
func (const-subst γ) _ = γ
_⇒_.naturality (const-subst γ) _ = refl

const-subst-cong : {γ1 γ2 : Γ ⟨ tt ⟩} → γ1 ≡ γ2 → const-subst {Γ = Γ} γ1 ≅ˢ const-subst γ2
eq (const-subst-cong eγ) tt = eγ

const-subst-natural : (δ : Δ ⟨ tt ⟩) (σ : Δ ⇒ Γ) → timeless-subst σ ⊚ const-subst δ ≅ˢ const-subst (func σ δ)
eq (const-subst-natural δ σ) _ = refl

global-ty : Ty (timeless-ctx Γ) → Ty Γ
type (global-ty T) tt γ = Tm ◇ (T [ const-subst γ ])
morph (global-ty {Γ = Γ} T) tt {γ}{γ'} eγ t = ι⁻¹[ proof ] t
  where
    proof : T [ const-subst γ ] ≅ᵗʸ T [ const-subst γ' ]
    proof = ty-subst-cong-subst (const-subst-cong (trans (sym (rel-id Γ γ)) eγ)) T
morph-cong (global-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
morph-id (global-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → trans (morph-cong T refl) (morph-id T _) })
morph-comp (global-ty T) tt tt eγ-zy eγ-yx t = tm-≅-to-≡
  (record { eq = λ _ → trans (morph-cong T (≤-irrelevant _ _)) (morph-comp T ≤-refl ≤-refl _ _ _) })

module _ {T : Ty (timeless-ctx Γ)} where
  global-tm : Tm (timeless-ctx Γ) T → Tm Γ (global-ty T)
  term (term (global-tm t) tt γ) n tt = t ⟨ n , γ ⟩'
  Tm.naturality (term (global-tm t) tt γ) m≤n refl = Tm.naturality t m≤n refl
  Tm.naturality (global-tm t) tt refl = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t ≤-refl _ })

  unglobal-tm : Tm Γ (global-ty T) → Tm (timeless-ctx Γ) T
  term (unglobal-tm t) n γ = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
  Tm.naturality (unglobal-tm t) m≤n refl = Tm.naturality (t ⟨ tt , _ ⟩') m≤n refl

  global-ty-β : (t : Tm (timeless-ctx Γ) T) → unglobal-tm (global-tm t) ≅ᵗᵐ t
  eq (global-ty-β t) _ = refl

  global-ty-η : (t : Tm Γ (global-ty T)) → global-tm (unglobal-tm t) ≅ᵗᵐ t
  eq (global-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

global-ty-cong : {T : Ty (timeless-ctx Γ)} {S : Ty (timeless-ctx Γ)} →
                 T ≅ᵗʸ S → global-ty T ≅ᵗʸ global-ty S
func (from (global-ty-cong T=S)) = ι⁻¹[ ty-subst-cong-ty (const-subst _) T=S ]_
CwF-Structure.naturality (from (global-ty-cong T=S)) _ = tm-≅-to-≡ (record { eq = λ _ → CwF-Structure.naturality (from T=S) _ })
func (to (global-ty-cong T=S)) = ι[ ty-subst-cong-ty (const-subst _) T=S ]_
CwF-Structure.naturality (to (global-ty-cong T=S)) _ = tm-≅-to-≡ (record { eq = λ _ → CwF-Structure.naturality (to T=S) _ })
eq (isoˡ (global-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symʳ (ty-subst-cong-ty (const-subst _) T=S) _)
eq (isoʳ (global-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symˡ (ty-subst-cong-ty (const-subst _) T=S) _)

ty-const-subst : (T : Ty (timeless-ctx Γ)) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                 (T [ timeless-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (timeless-subst σ) (const-subst _))
                                 (ty-subst-cong-subst (const-subst-natural _ σ) T)

global-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (timeless-ctx Γ)) → (global-ty T) [ σ ] ≅ᵗʸ global-ty (T [ timeless-subst σ ])
func (from (global-ty-natural σ T)) = ι[ ty-const-subst T σ _ ]_
CwF-Structure.naturality (from (global-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ →
  trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
func (to (global-ty-natural σ T)) = ι⁻¹[ ty-const-subst T σ _ ]_
CwF-Structure.naturality (to (global-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ →
  trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
eq (isoˡ (global-ty-natural σ T)) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
eq (isoʳ (global-ty-natural σ T)) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)

module _ (σ : Δ ⇒ Γ) {T : Ty (timeless-ctx Γ)} where
  global-tm-natural : (t : Tm (timeless-ctx Γ) T) →
                        (global-tm t) [ σ ]' ≅ᵗᵐ ι[ global-ty-natural σ T ] global-tm (t [ timeless-subst σ ]')
  eq (global-tm-natural t) _ = tm-≅-to-≡ (record { eq = λ _ → sym (morph-id T _) })

  unglobal-tm-natural : (t : Tm Γ (global-ty T)) →
                          (unglobal-tm t) [ timeless-subst σ ]' ≅ᵗᵐ unglobal-tm (ι⁻¹[ global-ty-natural σ T ] (t [ σ ]'))
  eq (unglobal-tm-natural t) _ = sym (morph-id T _)
