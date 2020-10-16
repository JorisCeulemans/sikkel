module GuardedRecursion.Modalities where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality renaming (subst to transp) hiding ([_])

open import Categories
open import CwF-Structure

private
  variable
    ℓ ℓ' : Level

module _ where
  private
    variable
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
  morph-cong (◬ T) e = morph-cong T refl
  morph-id (◬ T) t = trans (morph-cong T refl) (morph-id T t)
  morph-comp (◬ T) _ _ _ _ t = trans (morph-cong T refl) (morph-comp T tt tt _ _ t)

  module _ {T : Ty (⨅ Γ) ℓ} where
    ◬-intro : Tm (⨅ Γ) T → Tm Γ (◬ T)
    term (◬-intro t) n γ = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
    Tm.naturality (◬-intro t) _ _ = Tm.naturality t tt _

    ◬-elim : Tm Γ (◬ T) → Tm (⨅ Γ) T
    term (◬-elim t) _ γ = ctx-element-subst T (rel-id Γ γ) (t ⟨ 0 , γ ⟩')
    Tm.naturality (◬-elim t) tt refl = morph-id T _

    ◬-η : (t : Tm Γ (◬ T)) → ◬-intro (◬-elim t) ≅ᵗᵐ t
    eq (◬-η t) {n} γ =
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

    ◬-β : (t : Tm (⨅ Γ) T) → ◬-elim (◬-intro t) ≅ᵗᵐ t
    eq (◬-β t) γ = Tm.naturality t tt _

  ◬-natural : (σ : Δ ⇒ Γ) (T : Ty (⨅ Γ) ℓ) → (◬ T) [ σ ] ≅ᵗʸ ◬ (T [ ⨅-subst σ ])
  func (from (◬-natural σ T)) = ctx-element-subst T (_⇒_.naturality σ _)
  CwF-Structure.naturality (from (◬-natural σ T)) t =
    begin
      T ⟪ tt , _ ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , _ ⟫ t) ∎
    where open ≡-Reasoning
  func (to (◬-natural σ T)) = ctx-element-subst T (sym (_⇒_.naturality σ _))
  CwF-Structure.naturality (to (◬-natural σ T)) t =
    begin
      T ⟪ tt , _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _ ⟫ t) ∎
    where open ≡-Reasoning
  eq (isoˡ (◬-natural σ T)) t =
    begin
      T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , refl ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning
  eq (isoʳ (◬-natural σ T)) t =
    begin
      T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , refl ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning

  ◬-intro-natural : (σ : Δ ⇒ Γ) {T : Ty (⨅ Γ) ℓ} (t : Tm (⨅ Γ) T) →
                    (◬-intro t) [ σ ]' ≅ᵗᵐ ι[ ◬-natural σ T ] ◬-intro (t [ ⨅-subst σ ]')
  eq (◬-intro-natural σ t) δ = sym (Tm.naturality t tt _)

  ◬-elim-natural : (σ : Δ ⇒ Γ) {T : Ty (⨅ Γ) ℓ} (t : Tm Γ (◬ T)) →
                   (◬-elim t) [ ⨅-subst σ ]' ≅ᵗᵐ ◬-elim (ι⁻¹[ ◬-natural σ T ] (t [ σ ]'))
  eq (◬-elim-natural {Δ = Δ}{Γ = Γ} σ {T = T} t) δ =
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

  ▲ : Ctx ★ ℓ → Ctx ω ℓ
  set (▲ Γ) _ = Γ ⟨ tt ⟩
  rel (▲ Γ) _ γ = γ
  rel-id (▲ Γ) _ = refl
  rel-comp (▲ Γ) _ _ _ = refl

  ▲-subst : Δ ⇒ Γ → ▲ Δ ⇒ ▲ Γ
  func (▲-subst σ) = func σ
  _⇒_.naturality (▲-subst σ) _ = refl

  ▲-subst-id : ▲-subst (id-subst Γ) ≅ˢ id-subst (▲ Γ)
  eq ▲-subst-id _ = refl

  ▲-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → ▲-subst (σ ⊚ τ) ≅ˢ ▲-subst σ ⊚ ▲-subst τ
  eq (▲-subst-⊚ σ τ) _ = refl

  const-subst : Γ ⟨ tt ⟩ → ◇ ⇒ ▲ Γ
  func (const-subst γ) _ = γ
  _⇒_.naturality (const-subst γ) _ = refl

  ∇ : Ty (▲ Γ) ℓ → Ty Γ ℓ
  type (∇ T) _ γ = Tm ◇ (T [ const-subst γ ])
  morph (∇ {Γ = Γ} T) tt {γm}{γk} eγ t = MkTm tm nat
    where
      open ≡-Reasoning
      tm : (n : ℕ) → ⊤ → T ⟨ n , γk ⟩
      tm n _ = ctx-element-subst T (trans (sym (rel-id Γ γm)) eγ) (t ⟨ n , tt ⟩')
      nat : {m' n' : ℕ} (m≤n : m' ≤ n') {γn' : ⊤} {γm' : ⊤} (eγ' : γn' ≡ γm') →
            (T [ const-subst γk ]) ⟪ m≤n , eγ' ⟫ tm n' γn' ≡ tm m' γm'
      nat {m'}{n'} m≤n eγ' =
        begin
          T ⟪ m≤n , _ ⟫ (T ⟪ ≤-refl , _ ⟫ (t ⟨ n' , tt ⟩'))
        ≡˘⟨ morph-comp T m≤n ≤-refl _ _ _ ⟩
          T ⟪ ≤-trans m≤n ≤-refl , _ ⟫ (t ⟨ n' , tt ⟩')
        ≡⟨ morph-cong T (≤-irrelevant _ _) ⟩
          T ⟪ ≤-trans ≤-refl m≤n , _ ⟫ (t ⟨ n' , tt ⟩')
        ≡⟨ morph-comp T ≤-refl m≤n _ _ _ ⟩
          T ⟪ ≤-refl , _ ⟫ (T ⟪ m≤n , _ ⟫  (t ⟨ n' , tt ⟩'))
        ≡⟨ cong (T ⟪ ≤-refl , _ ⟫_) (Tm.naturality t m≤n refl) ⟩
          T ⟪ ≤-refl , _ ⟫ (t ⟨ m' , tt ⟩') ∎
  morph-cong (∇ T) e = {!!}
  morph-id (∇ T) = {!!}
  morph-comp (∇ T) = {!!}
