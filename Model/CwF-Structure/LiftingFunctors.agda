--------------------------------------------------
-- Lifting Functors
--
-- In this file we show that a functor from base categories C to D
--   can be lifted to a "strict" CwF endomorphism from Psh(D) to Psh(C).
--------------------------------------------------


open import Model.BaseCategory

module Model.CwF-Structure.LiftingFunctors {C D : BaseCategory} (F : Functor C D) where

open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure

open BaseCategory
open Functor


ctx-lift : Ctx D → Ctx C
ctx-lift Γ ⟨ c ⟩ = Γ ⟨ ob F c ⟩
ctx-lift Γ ⟪ f ⟫ γ = Γ ⟪ hom F f ⟫ γ
ctx-id (ctx-lift Γ) {γ = γ} =
  begin
    Γ ⟪ hom F (hom-id C) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (id-law F) ⟩
    Γ ⟪ hom-id D ⟫ γ
  ≡⟨ ctx-id Γ ⟩
    γ ∎
  where open ≡-Reasoning
ctx-comp (ctx-lift Γ) {f = f} {g} {γ} =
  begin
    Γ ⟪ hom F (g ∙[ C ] f) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (comp-law F) ⟩
    Γ ⟪ hom F g ∙[ D ] hom F f ⟫ γ
  ≡⟨ ctx-comp Γ ⟩
    Γ ⟪ hom F f ⟫ (Γ ⟪ hom F g ⟫ γ) ∎
  where open ≡-Reasoning

subst-lift : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) → ctx-lift Δ ⇒ ctx-lift Γ
func (subst-lift σ) {c} = func σ {ob F c}
naturality (subst-lift σ) {f = f} = naturality σ {f = hom F f}

subst-lift-id : {Γ : Ctx D} → subst-lift (id-subst Γ) ≅ˢ id-subst (ctx-lift Γ)
eq subst-lift-id _ = refl

subst-lift-comp : {Δ : Ctx D} {Γ : Ctx D} {Θ : Ctx D} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                  subst-lift (τ ⊚ σ) ≅ˢ subst-lift τ ⊚ subst-lift σ
eq (subst-lift-comp τ σ) _ = refl

ty-lift : {Γ : Ctx D} → Ty Γ → Ty (ctx-lift Γ)
ty-lift T ⟨ c , γ ⟩ = T ⟨ ob F c , γ ⟩
ty-lift T ⟪ f , eγ ⟫ t = T ⟪ hom F f , eγ ⟫ t
ty-cong (ty-lift T) e = ty-cong T (cong (hom F) e)
ty-id (ty-lift T) {t = t} =
  begin
    T ⟪ hom F (hom-id C) , _ ⟫ t
  ≡⟨ ty-cong T (id-law F) ⟩
    T ⟪ hom-id D , _ ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
 where open ≡-Reasoning
ty-comp (ty-lift T) {f = f} {g} {eγ-zy = eγ-zy} {eγ-yx} {t} =
  begin
    T ⟪ hom F (g ∙[ C ] f) , _ ⟫ t
  ≡⟨ ty-cong T (comp-law F) ⟩
    T ⟪ hom F g ∙[ D ] hom F f , _ ⟫ t
  ≡⟨ ty-comp T ⟩
    T ⟪ hom F f , eγ-yx ⟫ (T ⟪ hom F g , eγ-zy ⟫ t) ∎
  where open ≡-Reasoning

ty-lift-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) (T : Ty Γ) →
                  ty-lift (T [ σ ]) ≅ᵗʸ ty-lift T [ subst-lift σ ]
func (from (ty-lift-natural σ T)) = id
naturality (from (ty-lift-natural σ T)) = refl
func (to (ty-lift-natural σ T)) = id
naturality (to (ty-lift-natural σ T)) = refl
eq (isoˡ (ty-lift-natural σ T)) _ = refl
eq (isoʳ (ty-lift-natural σ T)) _ = refl

tm-lift : {Γ : Ctx D} {T : Ty Γ} → Tm Γ T → Tm (ctx-lift Γ) (ty-lift T)
tm-lift t ⟨ c , γ ⟩' = t ⟨ ob F c , γ ⟩'
naturality (tm-lift t) f eγ = naturality t (hom F f) eγ

tm-lift-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty Γ} (t : Tm Γ T) →
                  tm-lift (t [ σ ]') ≅ᵗᵐ ι[ ty-lift-natural σ T ] ((tm-lift t) [ subst-lift σ ]')
eq (tm-lift-natural σ t) δ = refl

lift-◇ : ctx-lift ◇ ≅ᶜ ◇
from lift-◇ = MkSubst id refl
to lift-◇ = MkSubst id refl
eq (isoˡ lift-◇) _ = refl
eq (isoʳ lift-◇) _ = refl

lift-ctx-ext : (Γ : Ctx D) (T : Ty Γ) → ctx-lift (Γ ,, T) ≅ᶜ ctx-lift Γ ,, ty-lift T
from (lift-ctx-ext Γ T) = MkSubst id refl
to (lift-ctx-ext Γ T) = MkSubst id refl
eq (isoˡ (lift-ctx-ext Γ T)) _ = refl
eq (isoʳ (lift-ctx-ext Γ T)) _ = refl

lift-π : (Γ : Ctx D) (T : Ty Γ) → subst-lift π ⊚ to (lift-ctx-ext Γ T) ≅ˢ π
eq (lift-π Γ T) _ = refl

lift-ξ : (Γ : Ctx D) (T : Ty Γ) → tm-lift ξ [ to (lift-ctx-ext Γ T) ]' ≅ᵗᵐ
                                     ι[ ty-subst-cong-ty (to (lift-ctx-ext Γ T)) (ty-lift-natural π T) ] (
                                     ι[ ty-subst-comp (ty-lift T) (subst-lift π) (to (lift-ctx-ext Γ T)) ] (
                                     ι[ ty-subst-cong-subst (lift-π Γ T) (ty-lift T) ] ξ))
eq (lift-ξ Γ T) [ γ , t ] = sym (
  begin
    T ⟪ hom F (hom-id C) , _ ⟫ t
  ≡⟨ ty-cong T (id-law F) ⟩
    T ⟪ hom-id D , _ ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎)
  where open ≡-Reasoning
