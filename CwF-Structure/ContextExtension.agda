--------------------------------------------------
-- Context extension
--------------------------------------------------

open import Categories

module CwF-Structure.ContextExtension {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (subst to transport)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

open Category C

infixl 15 _,,_

private
  variable
    ℓc ℓt ℓt' : Level
    Γ Δ Θ : Ctx C ℓ
    T S : Ty Γ ℓ


-- Definition of the extension of a context Γ with a type T.
-- In MLTT, this would be written as Γ, x : T.
_,,_ : (Γ : Ctx C ℓc) (T : Ty Γ ℓt) → Ctx C (ℓc ⊔ ℓt)
set (Γ ,, T) x = Σ[ γ ∈ Γ ⟨ x ⟩ ] (T ⟨ x , γ ⟩)
rel (Γ ,, T) f [ γ , t ] = [ Γ ⟪ f ⟫ γ , strict-morph T f γ t ]
rel-id (Γ ,, T) [ γ , t ] = to-Σ-eq (rel-id Γ γ) (strict-morph-id T t)
rel-comp (Γ ,, T) f g [ γ , t ] = to-Σ-eq (rel-comp Γ f g γ)
                                          (strict-morph-comp T f g t)

π : Γ ,, T ⇒ Γ
func π = proj₁
naturality π _ = refl

-- A term corresponding to the last variable in the context. In MLTT, this would be
-- written as Γ, x : T ⊢ x : T. Note that the type of the term is T [ π ] instead of
-- T because the latter is not a type in context Γ ,, T.
ξ : Tm (Γ ,, T) (T [ π ])
term ξ _ = proj₂
naturality ξ f refl = refl

-- In any cwf, there is by definition a one-to-one correspondence between substitutions
-- Δ ⇒ Γ ,, T and pairs of type Σ[ σ : Δ ⇒ Γ ] (Tm Δ (T [ σ ])). This is worked out
-- in the following functions.
ext-subst-to-subst : Δ ⇒ Γ ,, T → Δ ⇒ Γ
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term {T = T} τ = ι⁻¹[ ty-subst-comp T π τ ] (ξ [ τ ]')

to-ext-subst : (T : Ty Γ ℓ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
func (to-ext-subst T σ t) δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (to-ext-subst {Δ = Δ} T σ t) δ = to-Σ-eq (naturality σ δ) (
  begin
    transport (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
          (T ⟪ _ , refl ⟫ t ⟨ _ , δ ⟩')
  ≡⟨ morph-transport T refl (naturality σ δ) (t ⟨ _ , δ ⟩') ⟩
    T ⟪ _ , trans refl (naturality σ δ) ⟫ t ⟨ _ , δ ⟩'
  ≡⟨ morph-cong T refl _ _ ⟩
    T ⟪ _ , _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ naturality t _ refl ⟩
    t ⟨ _ , Δ ⟪ _ ⟫ δ ⟩' ∎)
  where open ≡-Reasoning

syntax to-ext-subst T σ t = ⟨ σ , t ∈ T ⟩

ctx-ext-subst-proj₁ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≅ˢ σ
eq (ctx-ext-subst-proj₁ σ t) δ = refl

ctx-ext-subst-proj₂ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                      ext-subst-to-term ⟨ σ , t ∈ T ⟩ ≅ᵗᵐ ι[ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) T ] t
eq (ctx-ext-subst-proj₂ {Γ = Γ}{T = T} σ t) δ = sym (
  begin
    T ⟪ hom-id , trans (rel-id Γ (func σ δ)) _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ morph-cong T refl _ _ ⟩
    T ⟪ hom-id , _ ⟫ (t ⟨ _ , δ ⟩')
  ≡⟨ morph-id T _ ⟩
    t ⟨ _ , δ ⟩' ∎)
  where open ≡-Reasoning

ctx-ext-subst-η : (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≅ˢ τ
eq (ctx-ext-subst-η τ) δ = refl

ctx-ext-subst-comp : (σ : Γ ⇒ Θ) (t : Tm Γ (T [ σ ])) (τ : Δ ⇒ Γ) →
                     ⟨ σ , t ∈ T ⟩ ⊚ τ ≅ˢ ⟨ σ ⊚ τ , ι⁻¹[ ty-subst-comp T σ τ ] (t [ τ ]') ∈ T ⟩
eq (ctx-ext-subst-comp σ t τ) δ = refl

-- Substitution of the last variable in context Γ ,, T with a term in Tm Γ T.
term-to-subst : Tm Γ T → Γ ⇒ Γ ,, T
term-to-subst {Γ = Γ}{T = T} t = ⟨ id-subst Γ , ι[ ty-subst-id T ] t ∈ T ⟩

_⊹ : (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = ⟨ σ ⊚ π , ι⁻¹[ ty-subst-comp T σ π ] ξ ∈ T ⟩

⊹-π-comm : (σ : Δ ⇒ Γ) → π {T = T} ⊚ (σ ⊹) ≅ˢ σ ⊚ π
eq (⊹-π-comm σ) δ = refl

ty-eq-to-ext-subst : (Γ : Ctx C ℓc) {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} →
                     T ≅ᵗʸ T' → Γ ,, T ⇒ Γ ,, T'
ty-eq-to-ext-subst Γ {T = T}{T'} T=T' = ⟨ π , ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ ∈ T' ⟩

{-
-- These functions are currently not used anywhere. We keep them in case we need them
-- in the future.
π-ext-comp-ty-subst : (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ ℓ) →
                      S [ π ] [ ⟨ σ , t ∈ T ⟩ ] ≅ᵗʸ S [ σ ]
π-ext-comp-ty-subst {T = T} σ t S =
  S [ π ] [ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-comp S π ⟨ σ , t ∈ T ⟩ ⟩
  S [ π ⊚ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) S ⟩
  S [ σ ] ∎
  where open ≅ᵗʸ-Reasoning

_⌈_⌋ : Tm (Γ ,, T) (S [ π ]) → Tm Γ T → Tm Γ S
_⌈_⌋ {Γ = Γ}{T = T}{S = S} s t = ι⁻¹[ proof ] (s [ term-to-subst t ]')
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
