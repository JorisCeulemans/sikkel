--------------------------------------------------
-- Context extension
--------------------------------------------------

module CwF-Structure.ContextExtension where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

infixl 15 _,,_


_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
set (Γ ,, T) n = Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) ineq [ γ , t ] = [ Γ ⟪ ineq ⟫ γ , strict-morph T ineq γ t ]
rel-id (Γ ,, T) [ γ , t ] = to-Σ-eq (rel-id Γ γ) (strict-morph-id T t)
rel-comp (Γ ,, T) k≤m m≤n [ γ , t ] = to-Σ-eq (rel-comp Γ k≤m m≤n γ)
                                              (strict-morph-comp T k≤m m≤n t)

π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π _ = refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π ])
term ξ _ = proj₂
naturality (ξ {T = T}) m≤n refl = refl
-- alternative for naturality without pattern matching on equality proof:
-- trans (sym (morph-subst T refl (cong proj₁ eγ) _))
--       (from-Σ-eq2 eγ)

ext-subst-to-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Δ ⇒ Γ
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : {Δ Γ : Ctx ℓ} {T : Ty Γ} (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term {T = T} τ = ι⁻¹[ ty-subst-comp T π τ ] (ξ [ τ ]')

to-ext-subst : {Δ Γ : Ctx ℓ} (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
func (to-ext-subst T σ t) δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (to-ext-subst {Δ = Δ}{Γ} T σ t) δ = to-Σ-eq (naturality σ δ)
  (begin
    subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
          (T ⟪ _ , refl ⟫ t ⟨ _ , δ ⟩')
  ≡⟨ morph-subst T refl (naturality σ δ) (t ⟨ _ , δ ⟩') ⟩
    T ⟪ _ , trans refl (naturality σ δ) ⟫ t ⟨ _ , δ ⟩'
  ≡⟨ morph-cong T refl _ _ ⟩
    T ⟪ _ , _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ naturality t _ refl ⟩
    t ⟨ _ , Δ ⟪ _ ⟫ δ ⟩' ∎)
  where open ≡-Reasoning

syntax to-ext-subst T σ t = ⟨ σ , t ∈ T ⟩

{-
to-ext-subst : {Δ Γ : Ctx ℓ} (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
to-ext-subst T σ t = MkSubst (λ δ → [ func σ δ , t ⟨ _ , δ ⟩' ])
                             (λ δ → to-Σ-eq (naturality σ δ)
                                             (trans (morph-subst T refl (naturality σ δ) (term t _ δ))
                                                    (trans (cong (λ x → T ⟪ _ , x ⟫ _) (sym (trans-reflʳ (naturality σ δ))))
                                                           (naturality t _ refl))))

to-ext-subst-Σ : {Δ Γ : Ctx ℓ} (T : Ty Γ) → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ])) → Δ ⇒ Γ ,, T
to-ext-subst-Σ T [ σ , t ] = to-ext-subst T σ t
-}

ctx-ext-subst-proj₁ : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≅ˢ σ
eq (ctx-ext-subst-proj₁ σ t) δ = refl

ctx-ext-subst-proj₂ : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                      ext-subst-to-term ⟨ σ , t ∈ T ⟩ ≅ᵗᵐ ι[ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) T ] t
eq (ctx-ext-subst-proj₂ {Γ = Γ}{T} σ t) δ = sym (
  begin
    T ⟪ ≤-refl , trans (rel-id Γ (func σ δ)) _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ morph-cong T refl _ _ ⟩
    T ⟪ ≤-refl , _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ morph-id T _ ⟩
    t ⟨ _ , δ ⟩' ∎)
  where open ≡-Reasoning

ctx-ext-subst-η : {Δ Γ : Ctx ℓ} {T : Ty Γ} (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≅ˢ τ
eq (ctx-ext-subst-η τ) δ = refl

ctx-ext-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (σ : Γ ⇒ Θ) (t : Tm Γ (T [ σ ])) (τ : Δ ⇒ Γ) →
                     ⟨ σ , t ∈ T ⟩ ⊚ τ ≅ˢ ⟨ σ ⊚ τ , ι⁻¹[ ty-subst-comp T σ τ ] (t [ τ ]') ∈ T ⟩
eq (ctx-ext-subst-comp σ t τ) δ = refl

term-to-subst : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Γ ⇒ Γ ,, T
term-to-subst {Γ = Γ}{T} t = ⟨ id-subst Γ , ι[ ty-subst-id T ] t ∈ T ⟩

π-ext-comp-ty-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ) →
                      S [ π ] [ ⟨ σ , t ∈ T ⟩ ] ≅ᵗʸ S [ σ ]
π-ext-comp-ty-subst {T = T} σ t S =
  S [ π ] [ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-comp S π ⟨ σ , t ∈ T ⟩ ⟩
  S [ π ⊚ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) S ⟩
  S [ σ ] ∎
  where open ≅ᵗʸ-Reasoning

{- TODO: check whether this is useful anywhere.
_⌈_⌋ : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ T → Tm Γ S
_⌈_⌋ {Γ = Γ}{T}{S} s t = subst (Tm Γ) proof (s [ to-ext-subst T (id-subst Γ) (t [ id-subst Γ ]') ]')
  where
    open ≡-Reasoning
    proof : S [ π ] [ to-ext-subst T (id-subst Γ) (t [ id-subst Γ ]') ] ≡ S
    proof =
      S [ π ] [ to-ext-subst T (id-subst Γ) (t [ id-subst Γ ]') ]
        ≡⟨ π-ext-comp-ty-subst {T = T} (id-subst Γ) (t [ id-subst Γ ]') S ⟩
      S [ id-subst Γ ]
        ≡⟨ ty-subst-id S ⟩
      S ∎
-}

_⊹ : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = ⟨ σ ⊚ π , ι⁻¹[ ty-subst-comp T σ π ] ξ ∈ T ⟩

⊹-π-comm : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) → π {T = T} ⊚ (σ ⊹) ≅ˢ σ ⊚ π
eq (⊹-π-comm σ) δ = refl
