--------------------------------------------------
-- Lifting Functors
--
-- In this file we show that a functor from C to D can be lifted to a
-- "strict" CwF endomorphism from Psh(D) to Psh(C).
--------------------------------------------------


open import Categories

module LiftingFunctors {C D : Category} (F : Functor C D) where

open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure

open Category
open Functor

private
  variable
    ℓ'' ℓt : Level

ctx-lift : Ctx D ℓ → Ctx C ℓ
set (ctx-lift Γ) c = Γ ⟨ ob F c ⟩
rel (ctx-lift Γ) f = Γ ⟪ hom F f ⟫
rel-id (ctx-lift Γ) γ =
  begin
    Γ ⟪ hom F (hom-id C) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (id-law F) ⟩
    Γ ⟪ hom-id D ⟫ γ
  ≡⟨ rel-id Γ γ ⟩
    γ ∎
  where open ≡-Reasoning
rel-comp (ctx-lift Γ) f g γ =
  begin
    Γ ⟪ hom F (g ∙[ C ] f) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (comp-law F) ⟩
    Γ ⟪ hom F g ∙[ D ] hom F f ⟫ γ
  ≡⟨ rel-comp Γ (hom F f) (hom F g) γ ⟩
    Γ ⟪ hom F f ⟫ (Γ ⟪ hom F g ⟫ γ) ∎
  where open ≡-Reasoning

subst-lift : {Δ : Ctx D ℓ} {Γ : Ctx D ℓ'} (σ : Δ ⇒ Γ) → ctx-lift Δ ⇒ ctx-lift Γ
func (subst-lift σ) {c} = func σ {ob F c}
naturality (subst-lift σ) {f = f} δ = naturality σ {f = hom F f} δ

subst-lift-id : {Γ : Ctx D ℓ} → subst-lift (id-subst Γ) ≅ˢ id-subst (ctx-lift Γ)
eq subst-lift-id _ = refl

subst-lift-comp : {Δ : Ctx D ℓ} {Γ : Ctx D ℓ'} {Θ : Ctx D ℓ''} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                  subst-lift (τ ⊚ σ) ≅ˢ subst-lift τ ⊚ subst-lift σ
eq (subst-lift-comp τ σ) _ = refl

ty-lift : {Γ : Ctx D ℓ} → Ty Γ ℓt → Ty (ctx-lift Γ) ℓt
type (ty-lift T) c γ = T ⟨ ob F c , γ ⟩
morph (ty-lift T) f eγ t = T ⟪ hom F f , eγ ⟫ t
morph-id (ty-lift T) t =
  begin
    T ⟪ hom F (hom-id C) , _ ⟫ t
  ≡⟨ morph-cong T (id-law F) _ _ ⟩
    T ⟪ hom-id D , _ ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
 where open ≡-Reasoning
morph-comp (ty-lift T) f g eq-zy eq-yx t =
  begin
    T ⟪ hom F (g ∙[ C ] f) , _ ⟫ t
  ≡⟨ morph-cong T (comp-law F) _ _ ⟩
    T ⟪ hom F g ∙[ D ] hom F f , _ ⟫ t
  ≡⟨ morph-comp T (hom F f) (hom F g) eq-zy eq-yx t ⟩
    T ⟪ hom F f , eq-yx ⟫ (T ⟪ hom F g , eq-zy ⟫ t) ∎
  where open ≡-Reasoning

ty-lift-natural : {Δ : Ctx D ℓ} {Γ : Ctx D ℓ'} (σ : Δ ⇒ Γ) (T : Ty Γ ℓt) →
                  ty-lift (T [ σ ]) ≅ᵗʸ ty-lift T [ subst-lift σ ]
from (ty-lift-natural σ T) = record { func = id ; naturality = λ _ → refl }
to (ty-lift-natural σ T) = record { func = id ; naturality = λ _ → refl }
eq (isoˡ (ty-lift-natural σ T)) _ = refl
eq (isoʳ (ty-lift-natural σ T)) _ = refl

tm-lift : {Γ : Ctx D ℓ} {T : Ty Γ ℓt} → Tm Γ T → Tm (ctx-lift Γ) (ty-lift T)
term (tm-lift t) c γ = t ⟨ ob F c , γ ⟩'
naturality (tm-lift t) f eγ = naturality t (hom F f) eγ

tm-lift-natural : {Δ : Ctx D ℓ} {Γ : Ctx D ℓ'} (σ : Δ ⇒ Γ) {T : Ty Γ ℓt} (t : Tm Γ T) →
                  tm-lift (t [ σ ]') ≅ᵗᵐ ι[ ty-lift-natural σ T ] ((tm-lift t) [ subst-lift σ ]')
eq (tm-lift-natural σ t) δ = refl

lift-◇ : ctx-lift ◇ ≅ᶜ ◇
from lift-◇ = MkSubst id (λ _ → refl)
to lift-◇ = MkSubst id (λ _ → refl)
eq (isoˡ lift-◇) _ = refl
eq (isoʳ lift-◇) _ = refl

lift-ctx-ext : (Γ : Ctx D ℓ) (T : Ty Γ ℓt) → ctx-lift (Γ ,, T) ≅ᶜ ctx-lift Γ ,, ty-lift T
from (lift-ctx-ext Γ T) = MkSubst id (λ _ → refl)
to (lift-ctx-ext Γ T) = MkSubst id (λ _ → refl)
eq (isoˡ (lift-ctx-ext Γ T)) _ = refl
eq (isoʳ (lift-ctx-ext Γ T)) _ = refl

lift-π : (Γ : Ctx D ℓ) (T : Ty Γ ℓt) → subst-lift π ⊚ to (lift-ctx-ext Γ T) ≅ˢ π
eq (lift-π Γ T) _ = refl

lift-ξ : (Γ : Ctx D ℓ) (T : Ty Γ ℓt) → tm-lift ξ [ to (lift-ctx-ext Γ T) ]' ≅ᵗᵐ
                                     ι[ ty-subst-cong-ty (to (lift-ctx-ext Γ T)) (ty-lift-natural π T) ] (
                                     ι[ ty-subst-comp (ty-lift T) (subst-lift π) (to (lift-ctx-ext Γ T)) ] (
                                     ι[ ty-subst-cong-subst (lift-π Γ T) (ty-lift T) ] ξ))
eq (lift-ξ Γ T) [ γ , t ] = sym (
  begin
    T ⟪ hom F (hom-id C) , _ ⟫ t
  ≡⟨ morph-cong T (id-law F) _ _ ⟩
    T ⟪ hom-id D , _ ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎)
  where open ≡-Reasoning
