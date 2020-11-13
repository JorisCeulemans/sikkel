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

  repeat-ty : Ty (now Γ) ℓ' → Ty Γ ℓ'
  type (repeat-ty {Γ = Γ} T) n γ = T ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩
  morph (repeat-ty {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ = T ⟪ tt , proof ⟫
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
  morph-cong (repeat-ty T) e = morph-cong T refl
  morph-id (repeat-ty T) t = trans (morph-cong T refl) (morph-id T t)
  morph-comp (repeat-ty T) _ _ _ _ t = trans (morph-cong T refl) (morph-comp T tt tt _ _ t)

  module _ {T : Ty (now Γ) ℓ} where
    repeat-tm : Tm (now Γ) T → Tm Γ (repeat-ty T)
    term (repeat-tm t) n γ = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
    Tm.naturality (repeat-tm t) _ _ = Tm.naturality t tt _

    unrepeat-tm : Tm Γ (repeat-ty T) → Tm (now Γ) T
    term (unrepeat-tm t) _ γ = ctx-element-subst T (rel-id Γ γ) (t ⟨ 0 , γ ⟩')
    Tm.naturality (unrepeat-tm t) tt refl = morph-id T _

    repeat-ty-η : (t : Tm Γ (repeat-ty T)) → repeat-tm (unrepeat-tm t) ≅ᵗᵐ t
    eq (repeat-ty-η t) {n} γ =
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

    repeat-ty-β : (t : Tm (now Γ) T) → unrepeat-tm (repeat-tm t) ≅ᵗᵐ t
    eq (repeat-ty-β t) γ = Tm.naturality t tt _

  repeat-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (now Γ) ℓ) → (repeat-ty T) [ σ ] ≅ᵗʸ repeat-ty (T [ now-subst σ ])
  func (from (repeat-ty-natural σ T)) = ctx-element-subst T (_⇒_.naturality σ _)
  CwF-Structure.naturality (from (repeat-ty-natural σ T)) t =
    begin
      T ⟪ tt , _ ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , _ ⟫ t) ∎
    where open ≡-Reasoning
  func (to (repeat-ty-natural σ T)) = ctx-element-subst T (sym (_⇒_.naturality σ _))
  CwF-Structure.naturality (to (repeat-ty-natural σ T)) t =
    begin
      T ⟪ tt , _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _ ⟫ t) ∎
    where open ≡-Reasoning
  eq (isoˡ (repeat-ty-natural σ T)) t =
    begin
      T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , refl ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning
  eq (isoʳ (repeat-ty-natural σ T)) t =
    begin
      T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , refl ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning

  repeat-tm-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ} (t : Tm (now Γ) T) →
                    (repeat-tm t) [ σ ]' ≅ᵗᵐ ι[ repeat-ty-natural σ T ] repeat-tm (t [ now-subst σ ]')
  eq (repeat-tm-natural σ t) δ = sym (Tm.naturality t tt _)

  unrepeat-tm-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ} (t : Tm Γ (repeat-ty T)) →
                   (unrepeat-tm t) [ now-subst σ ]' ≅ᵗᵐ unrepeat-tm (ι⁻¹[ repeat-ty-natural σ T ] (t [ σ ]'))
  eq (unrepeat-tm-natural {Δ = Δ}{Γ = Γ} σ {T = T} t) δ =
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

  repeat-ctx : Ctx ★ ℓ → Ctx ω ℓ
  set (repeat-ctx Γ) _ = Γ ⟨ tt ⟩
  rel (repeat-ctx Γ) _ γ = γ
  rel-id (repeat-ctx Γ) _ = refl
  rel-comp (repeat-ctx Γ) _ _ _ = refl

  repeat-subst : Δ ⇒ Γ → repeat-ctx Δ ⇒ repeat-ctx Γ
  func (repeat-subst σ) = func σ
  _⇒_.naturality (repeat-subst σ) _ = refl

  repeat-subst-id : repeat-subst (id-subst Γ) ≅ˢ id-subst (repeat-ctx Γ)
  eq repeat-subst-id _ = refl

  repeat-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → repeat-subst (σ ⊚ τ) ≅ˢ repeat-subst σ ⊚ repeat-subst τ
  eq (repeat-subst-⊚ σ τ) _ = refl

  const-subst : Γ ⟨ tt ⟩ → ◇ ⇒ repeat-ctx Γ
  func (const-subst γ) _ = γ
  _⇒_.naturality (const-subst γ) _ = refl

  const-subst-cong : {γ1 γ2 : Γ ⟨ tt ⟩} → γ1 ≡ γ2 → const-subst {Γ = Γ} γ1 ≅ˢ const-subst γ2
  eq (const-subst-cong eγ) tt = eγ

  const-subst-natural : (δ : Δ ⟨ tt ⟩) (σ : Δ ⇒ Γ) → repeat-subst σ ⊚ const-subst δ ≅ˢ const-subst (func σ δ)
  eq (const-subst-natural δ σ) _ = refl

  collapse-ty : Ty (repeat-ctx Γ) ℓ → Ty Γ ℓ
  type (collapse-ty T) tt γ = Tm ◇ (T [ const-subst γ ])
  morph (collapse-ty {Γ = Γ} T) tt {γ}{γ'} eγ t = ι⁻¹[ proof ] t
    where
      proof : T [ const-subst γ ] ≅ᵗʸ T [ const-subst γ' ]
      proof = ty-subst-cong-subst (const-subst-cong (trans (sym (rel-id Γ γ)) eγ)) T
  morph-cong (collapse-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
  morph-id (collapse-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → trans (morph-cong T refl) (morph-id T _) })
  morph-comp (collapse-ty T) tt tt eγ-zy eγ-yx t = tm-≅-to-≡
    (record { eq = λ _ → trans (morph-cong T (≤-irrelevant _ _)) (morph-comp T ≤-refl ≤-refl _ _ _) })

  module _ {T : Ty (repeat-ctx Γ) ℓ} where
    collapse-tm : Tm (repeat-ctx Γ) T → Tm Γ (collapse-ty T)
    term (term (collapse-tm t) tt γ) n tt = t ⟨ n , γ ⟩'
    Tm.naturality (term (collapse-tm t) tt γ) m≤n refl = Tm.naturality t m≤n refl
    Tm.naturality (collapse-tm t) tt refl = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t ≤-refl _ })

    uncollapse-tm : Tm Γ (collapse-ty T) → Tm (repeat-ctx Γ) T
    term (uncollapse-tm t) n γ = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
    Tm.naturality (uncollapse-tm t) m≤n refl = Tm.naturality (t ⟨ tt , _ ⟩') m≤n refl

    collapse-ty-β : (t : Tm (repeat-ctx Γ) T) → uncollapse-tm (collapse-tm t) ≅ᵗᵐ t
    eq (collapse-ty-β t) _ = refl

    collapse-ty-η : (t : Tm Γ (collapse-ty T)) → collapse-tm (uncollapse-tm t) ≅ᵗᵐ t
    eq (collapse-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

  ty-const-subst : (T : Ty (repeat-ctx Γ) ℓ) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                   (T [ repeat-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
  ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (repeat-subst σ) (const-subst _))
                                   (ty-subst-cong-subst (const-subst-natural _ σ) T)

  collapse-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (repeat-ctx Γ) ℓ) → (collapse-ty T) [ σ ] ≅ᵗʸ collapse-ty (T [ repeat-subst σ ])
  func (from (collapse-ty-natural σ T)) = ι[ ty-const-subst T σ _ ]_
  CwF-Structure.naturality (from (collapse-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ → 
    trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
  func (to (collapse-ty-natural σ T)) = ι⁻¹[ ty-const-subst T σ _ ]_
  CwF-Structure.naturality (to (collapse-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ →
    trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
  eq (isoˡ (collapse-ty-natural σ T)) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
  eq (isoʳ (collapse-ty-natural σ T)) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)
