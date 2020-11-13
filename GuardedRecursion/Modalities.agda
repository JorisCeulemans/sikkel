module GuardedRecursion.Modalities where

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

module _ where
  private
    variable
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


module _ where
  private
    variable
      Δ Γ Θ : Ctx ★ ℓ

  timeless-ctx : Ctx ★ ℓ → Ctx ω ℓ
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

  collapse-ty : Ty (timeless-ctx Γ) ℓ → Ty Γ ℓ
  type (collapse-ty T) tt γ = Tm ◇ (T [ const-subst γ ])
  morph (collapse-ty {Γ = Γ} T) tt {γ}{γ'} eγ t = ι⁻¹[ proof ] t
    where
      proof : T [ const-subst γ ] ≅ᵗʸ T [ const-subst γ' ]
      proof = ty-subst-cong-subst (const-subst-cong (trans (sym (rel-id Γ γ)) eγ)) T
  morph-cong (collapse-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
  morph-id (collapse-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → trans (morph-cong T refl) (morph-id T _) })
  morph-comp (collapse-ty T) tt tt eγ-zy eγ-yx t = tm-≅-to-≡
    (record { eq = λ _ → trans (morph-cong T (≤-irrelevant _ _)) (morph-comp T ≤-refl ≤-refl _ _ _) })

  module _ {T : Ty (timeless-ctx Γ) ℓ} where
    collapse-tm : Tm (timeless-ctx Γ) T → Tm Γ (collapse-ty T)
    term (term (collapse-tm t) tt γ) n tt = t ⟨ n , γ ⟩'
    Tm.naturality (term (collapse-tm t) tt γ) m≤n refl = Tm.naturality t m≤n refl
    Tm.naturality (collapse-tm t) tt refl = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t ≤-refl _ })

    uncollapse-tm : Tm Γ (collapse-ty T) → Tm (timeless-ctx Γ) T
    term (uncollapse-tm t) n γ = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
    Tm.naturality (uncollapse-tm t) m≤n refl = Tm.naturality (t ⟨ tt , _ ⟩') m≤n refl

    collapse-ty-β : (t : Tm (timeless-ctx Γ) T) → uncollapse-tm (collapse-tm t) ≅ᵗᵐ t
    eq (collapse-ty-β t) _ = refl

    collapse-ty-η : (t : Tm Γ (collapse-ty T)) → collapse-tm (uncollapse-tm t) ≅ᵗᵐ t
    eq (collapse-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

  ty-const-subst : (T : Ty (timeless-ctx Γ) ℓ) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                   (T [ timeless-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
  ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (timeless-subst σ) (const-subst _))
                                   (ty-subst-cong-subst (const-subst-natural _ σ) T)

  collapse-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (timeless-ctx Γ) ℓ) → (collapse-ty T) [ σ ] ≅ᵗʸ collapse-ty (T [ timeless-subst σ ])
  func (from (collapse-ty-natural σ T)) = ι[ ty-const-subst T σ _ ]_
  CwF-Structure.naturality (from (collapse-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ → 
    trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
  func (to (collapse-ty-natural σ T)) = ι⁻¹[ ty-const-subst T σ _ ]_
  CwF-Structure.naturality (to (collapse-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ →
    trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
  eq (isoˡ (collapse-ty-natural σ T)) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
  eq (isoʳ (collapse-ty-natural σ T)) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)

  module _ (σ : Δ ⇒ Γ) {T : Ty (timeless-ctx Γ) ℓ} where
    collapse-tm-natural : (t : Tm (timeless-ctx Γ) T) →
                          (collapse-tm t) [ σ ]' ≅ᵗᵐ ι[ collapse-ty-natural σ T ] collapse-tm (t [ timeless-subst σ ]')
    eq (collapse-tm-natural t) _ = tm-≅-to-≡ (record { eq = λ _ → sym (morph-id T _) })

    uncollapse-tm-natural : (t : Tm Γ (collapse-ty T)) →
                            (uncollapse-tm t) [ timeless-subst σ ]' ≅ᵗᵐ uncollapse-tm (ι⁻¹[ collapse-ty-natural σ T ] (t [ σ ]'))
    eq (uncollapse-tm-natural t) _ = sym (morph-id T _)
