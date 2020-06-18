--------------------------------------------------
-- Context extension
--------------------------------------------------

open import Categories

module CwF-Structure.ContextExtension {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types {C = C}
open import CwF-Structure.Terms {C = C}

open Category C

infixl 15 _,,_

private
  variable
    Γ Δ Θ : Ctx C ℓ


-- Definition of the extension of a context Γ with a type T.
-- In MLTT, this would be written as Γ, x : T.
_,,_ : (Γ : Ctx C ℓ) (T : Ty Γ) → Ctx C ℓ
set (Γ ,, T) x = Σ[ γ ∈ Γ ⟨ x ⟩ ] (T ⟨ x , γ ⟩)
rel (Γ ,, T) f [ γ , t ] = [ Γ ⟪ f ⟫ γ , strict-morph T f γ t ]
rel-id (Γ ,, T) [ γ , t ] = to-Σ-eq (rel-id Γ γ) (strict-morph-id T t)
rel-comp (Γ ,, T) f g [ γ , t ] = to-Σ-eq (rel-comp Γ f g γ)
                                          (strict-morph-comp T f g t)

π : {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π _ = refl

-- A term corresponding to the last variable in the context. In MLTT, this would be
-- written as Γ, x : T ⊢ x : T. Note that the type of the term is T [ π ] instead of
-- T because the latter is not a type in context Γ ,, T.
ξ : {T : Ty Γ} → Tm (Γ ,, T) (T [ π ])
term ξ _ = proj₂
naturality ξ f refl = refl

-- In any cwf, there is by definition a one-to-one correspondence between substitutions
-- Δ ⇒ Γ ,, T and pairs of type Σ[ σ : Δ ⇒ Γ ] (Tm Δ (T [ σ ])). This is worked out
-- in the following functions.
ext-subst-to-subst : {T : Ty Γ} → Δ ⇒ Γ ,, T → Δ ⇒ Γ
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : {T : Ty Γ} (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term {T = T} τ = ι⁻¹[ ty-subst-comp T π τ ] (ξ [ τ ]')

to-ext-subst : (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
func (to-ext-subst T σ t) δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (to-ext-subst {Δ = Δ} T σ t) δ = to-Σ-eq (naturality σ δ) (
  begin
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

ctx-ext-subst-proj₁ : {T : Ty Γ} (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≅ˢ σ
eq (ctx-ext-subst-proj₁ σ t) δ = refl

ctx-ext-subst-proj₂ : {T : Ty Γ} (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                      ext-subst-to-term ⟨ σ , t ∈ T ⟩ ≅ᵗᵐ ι[ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) T ] t
eq (ctx-ext-subst-proj₂ {Γ = Γ}{T = T} σ t) δ = sym (
  begin
    T ⟪ hom-id , trans (rel-id Γ (func σ δ)) _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ morph-cong T refl _ _ ⟩
    T ⟪ hom-id , _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ morph-id T _ ⟩
    t ⟨ _ , δ ⟩' ∎)
  where open ≡-Reasoning

ctx-ext-subst-η : {T : Ty Γ} (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≅ˢ τ
eq (ctx-ext-subst-η τ) δ = refl

ctx-ext-subst-comp : {T : Ty Θ} (σ : Γ ⇒ Θ) (t : Tm Γ (T [ σ ])) (τ : Δ ⇒ Γ) →
                     ⟨ σ , t ∈ T ⟩ ⊚ τ ≅ˢ ⟨ σ ⊚ τ , ι⁻¹[ ty-subst-comp T σ τ ] (t [ τ ]') ∈ T ⟩
eq (ctx-ext-subst-comp σ t τ) δ = refl

-- Substitution of the last variable in context Γ ,, T with a term in Tm Γ T.
term-to-subst : {T : Ty Γ} → Tm Γ T → Γ ⇒ Γ ,, T
term-to-subst {Γ = Γ}{T} t = ⟨ id-subst Γ , ι[ ty-subst-id T ] t ∈ T ⟩

_⊹ : {T : Ty Γ} (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = ⟨ σ ⊚ π , ι⁻¹[ ty-subst-comp T σ π ] ξ ∈ T ⟩

⊹-π-comm : {T : Ty Γ} (σ : Δ ⇒ Γ) → π {T = T} ⊚ (σ ⊹) ≅ˢ σ ⊚ π
eq (⊹-π-comm σ) δ = refl

ty-eq-to-ext-subst : (Γ : Ctx C ℓ) {T T' : Ty Γ} → T ≅ᵗʸ T' → Γ ,, T ⇒ Γ ,, T'
ty-eq-to-ext-subst Γ {T = T}{T'} T=T' = ⟨ π , ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ ∈ T' ⟩

{-
-- These functions are currently not used anywhere. We keep them in case we need them
-- in the future.
π-ext-comp-ty-subst : {Δ Γ : Ctx C ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ) →
                      S [ π ] [ ⟨ σ , t ∈ T ⟩ ] ≅ᵗʸ S [ σ ]
π-ext-comp-ty-subst {T = T} σ t S =
  S [ π ] [ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-comp S π ⟨ σ , t ∈ T ⟩ ⟩
  S [ π ⊚ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) S ⟩
  S [ σ ] ∎
  where open ≅ᵗʸ-Reasoning

_⌈_⌋ : {Γ : Ctx C ℓ} {T S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ T → Tm Γ S
_⌈_⌋ {Γ = Γ}{T}{S} s t = ι⁻¹[ proof ] (s [ term-to-subst t ]')
  where
    open ≅ᵗʸ-Reasoning
    proof : S [ π ] [ term-to-subst t ] ≅ᵗʸ S
    proof =
      S [ π ] [ term-to-subst t ]
        ≅⟨ π-ext-comp-ty-subst (id-subst Γ) (ι[ ty-subst-id T ] t) S ⟩
      S [ id-subst Γ ]
        ≅⟨ ty-subst-id S ⟩
      S ∎
-}
