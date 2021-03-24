--------------------------------------------------
-- The timeless-allnow dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.AllNow where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure

private
  variable
    Δ Γ Θ : Ctx ★


timeless-ctx : Ctx ★ → Ctx ω
timeless-ctx Γ ⟨ _ ⟩ = Γ ⟨ tt ⟩
timeless-ctx Γ ⟪ _ ⟫ γ = γ
ctx-id (timeless-ctx Γ) _ = refl
ctx-comp (timeless-ctx Γ) _ _ _ = refl

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

allnow-ty : Ty (timeless-ctx Γ) → Ty Γ
allnow-ty T ⟨ tt , γ ⟩ = Tm ◇ (T [ const-subst γ ])
_⟪_,_⟫_ (allnow-ty {Γ = Γ} T) tt {γ}{γ'} eγ t = ι⁻¹[ proof ] t
  where
    proof : T [ const-subst γ ] ≅ᵗʸ T [ const-subst γ' ]
    proof = ty-subst-cong-subst (const-subst-cong (trans (sym (ctx-id Γ γ)) eγ)) T
ty-cong (allnow-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
ty-id (allnow-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → trans (ty-cong T refl) (ty-id T _) })
ty-comp (allnow-ty T) tt tt eγ-zy eγ-yx t = tm-≅-to-≡
  (record { eq = λ _ → trans (ty-cong T (≤-irrelevant _ _)) (ty-comp T ≤-refl ≤-refl _ _ _) })

module _ {T : Ty (timeless-ctx Γ)} where
  allnow-tm : Tm (timeless-ctx Γ) T → Tm Γ (allnow-ty T)
  (allnow-tm t ⟨ tt , γ ⟩') ⟨ n , tt ⟩' = t ⟨ n , γ ⟩'
  Tm.naturality (allnow-tm t ⟨ tt , γ ⟩') m≤n refl = Tm.naturality t m≤n refl
  Tm.naturality (allnow-tm t) tt refl = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t ≤-refl _ })

  unallnow-tm : Tm Γ (allnow-ty T) → Tm (timeless-ctx Γ) T
  unallnow-tm t ⟨ n , γ ⟩' = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
  Tm.naturality (unallnow-tm t) m≤n refl = Tm.naturality (t ⟨ tt , _ ⟩') m≤n refl

  allnow-ty-β : (t : Tm (timeless-ctx Γ) T) → unallnow-tm (allnow-tm t) ≅ᵗᵐ t
  eq (allnow-ty-β t) _ = refl

  allnow-ty-η : (t : Tm Γ (allnow-ty T)) → allnow-tm (unallnow-tm t) ≅ᵗᵐ t
  eq (allnow-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

allnow-ty-cong : {T : Ty (timeless-ctx Γ)} {S : Ty (timeless-ctx Γ)} →
                 T ≅ᵗʸ S → allnow-ty T ≅ᵗʸ allnow-ty S
func (from (allnow-ty-cong T=S)) = ι⁻¹[ ty-subst-cong-ty (const-subst _) T=S ]_
CwF-Structure.naturality (from (allnow-ty-cong T=S)) _ = tm-≅-to-≡ (record { eq = λ _ → CwF-Structure.naturality (from T=S) _ })
func (to (allnow-ty-cong T=S)) = ι[ ty-subst-cong-ty (const-subst _) T=S ]_
CwF-Structure.naturality (to (allnow-ty-cong T=S)) _ = tm-≅-to-≡ (record { eq = λ _ → CwF-Structure.naturality (to T=S) _ })
eq (isoˡ (allnow-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symʳ (ty-subst-cong-ty (const-subst _) T=S) _)
eq (isoʳ (allnow-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symˡ (ty-subst-cong-ty (const-subst _) T=S) _)

module _ {T : Ty (timeless-ctx Γ)} where
  allnow-tm-cong : {t s : Tm (timeless-ctx Γ) T} → t ≅ᵗᵐ s → allnow-tm t ≅ᵗᵐ allnow-tm s
  eq (allnow-tm-cong t=s) γ = tm-≅-to-≡ (record { eq = λ _ → eq t=s γ })

  unallnow-tm-cong : {t s : Tm Γ (allnow-ty T)} → t ≅ᵗᵐ s → unallnow-tm t ≅ᵗᵐ unallnow-tm s
  eq (unallnow-tm-cong t=s) γ = cong (λ - → - ⟨ _ , tt ⟩') (eq t=s γ)

ty-const-subst : (T : Ty (timeless-ctx Γ)) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                 (T [ timeless-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (timeless-subst σ) (const-subst _))
                                 (ty-subst-cong-subst (const-subst-natural _ σ) T)

allnow-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (timeless-ctx Γ)} → (allnow-ty T) [ σ ] ≅ᵗʸ allnow-ty (T [ timeless-subst σ ])
func (from (allnow-ty-natural σ {T})) = ι[ ty-const-subst T σ _ ]_
CwF-Structure.naturality (from (allnow-ty-natural σ {T})) t = tm-≅-to-≡ (record { eq = λ _ → ty-cong-2-2 T refl })
func (to (allnow-ty-natural σ {T})) = ι⁻¹[ ty-const-subst T σ _ ]_
CwF-Structure.naturality (to (allnow-ty-natural σ {T})) t = tm-≅-to-≡ (record { eq = λ _ → ty-cong-2-2 T refl })
eq (isoˡ (allnow-ty-natural σ {T})) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
eq (isoʳ (allnow-ty-natural σ {T})) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)

module _ (σ : Δ ⇒ Γ) {T : Ty (timeless-ctx Γ)} where
  allnow-tm-natural : (t : Tm (timeless-ctx Γ) T) →
                        (allnow-tm t) [ σ ]' ≅ᵗᵐ ι[ allnow-ty-natural σ ] allnow-tm (t [ timeless-subst σ ]')
  eq (allnow-tm-natural t) _ = tm-≅-to-≡ (record { eq = λ _ → sym (ty-id T _) })

  unallnow-tm-natural : (t : Tm Γ (allnow-ty T)) →
                          (unallnow-tm t) [ timeless-subst σ ]' ≅ᵗᵐ unallnow-tm (ι⁻¹[ allnow-ty-natural σ ] (t [ σ ]'))
  eq (unallnow-tm-natural t) _ = sym (ty-id T _)
