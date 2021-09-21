--------------------------------------------------
-- Proofs about the interactions between the different
-- modalities for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Interaction where

open import Data.Nat
open import Data.Unit
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Modality
open import Applications.GuardedRecursion.Model.Modalities.Later
open import Applications.GuardedRecursion.Model.Modalities.Timeless
open import Applications.GuardedRecursion.Model.Modalities.AllNow
open import Applications.GuardedRecursion.Model.Modalities.Bundles


--------------------------------------------------
-- Interaction between the later and unit modalities

𝟙≤later : TwoCell 𝟙 later
transf-op (transf 𝟙≤later) = from-earlier
CtxNatTransf.naturality (transf 𝟙≤later) = from-earlier-natural


--------------------------------------------------
-- Interaction between the allnow and later modalities

earlier-timeless-ctx : (Γ : Ctx ★) → ◄ (timeless-ctx Γ) ≅ᶜ timeless-ctx Γ
from (earlier-timeless-ctx Γ) = from-earlier (timeless-ctx Γ)
func (to (earlier-timeless-ctx Γ)) γ = γ
_⇒_.naturality (to (earlier-timeless-ctx Γ)) = refl
eq (isoˡ (earlier-timeless-ctx Γ)) _ = refl
eq (isoʳ (earlier-timeless-ctx Γ)) _ = refl

allnow-later-tyʳ : {Γ : Ctx ★} (T : Ty (◄ (timeless-ctx Γ))) →
                  allnow-ty (▻ T) ≅ᵗʸ allnow-ty (T [ to (earlier-timeless-ctx Γ) ])
func (from (allnow-later-tyʳ T)) t ⟨ n , _ ⟩' = t ⟨ suc n , tt ⟩'
Tm.naturality (func (from (allnow-later-tyʳ T)) t) m≤n _ = trans (ty-cong T refl) (Tm.naturality t (s≤s m≤n) refl)
_↣_.naturality (from (allnow-later-tyʳ T)) = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
func (to (allnow-later-tyʳ T)) t ⟨ zero  , _ ⟩' = _
func (to (allnow-later-tyʳ T)) t ⟨ suc n , _ ⟩' = t ⟨ n , tt ⟩'
Tm.naturality (func (to (allnow-later-tyʳ T)) t) z≤n _ = refl
Tm.naturality (func (to (allnow-later-tyʳ T)) t) (s≤s m≤n) _ = trans (ty-cong T refl) (Tm.naturality t m≤n refl)
_↣_.naturality (to (allnow-later-tyʳ T)) = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → ty-cong T refl } })
eq (isoˡ (allnow-later-tyʳ T)) t = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → refl } })
eq (isoʳ (allnow-later-tyʳ T)) t = tm-≅-to-≡ (record { eq = λ _ → refl })

allnow-later : allnow ⓜ later ≅ᵐ allnow
eq-lock allnow-later = earlier-timeless-ctx
eq-mod-tyʳ allnow-later = allnow-later-tyʳ

allnow-later'-ty : {Γ : Ctx ★} (T : Ty (timeless-ctx Γ)) →
                   allnow-ty (▻' T) ≅ᵗʸ allnow-ty T
allnow-later'-ty = eq-mod-tyˡ allnow-later


--------------------------------------------------
-- Interaction between the allnow and timeless modalities

now-timeless-ctx : (Γ : Ctx ★) → now (timeless-ctx Γ) ≅ᶜ Γ
func (from (now-timeless-ctx Γ)) = id
_⇒_.naturality (from (now-timeless-ctx Γ)) {f = tt} = ctx-id Γ
func (to (now-timeless-ctx Γ)) = id
_⇒_.naturality (to (now-timeless-ctx Γ)) {f = tt} = sym (ctx-id Γ)
eq (isoˡ (now-timeless-ctx Γ)) _ = refl
eq (isoʳ (now-timeless-ctx Γ)) _ = refl

now-timeless-natural : {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) →
                       from (now-timeless-ctx Γ) ⊚ now-subst (timeless-subst σ) ≅ˢ σ ⊚ from (now-timeless-ctx Δ)
eq (now-timeless-natural σ) _ = refl

allnow-timeless-tyʳ : {Γ : Ctx ★} (T : Ty (now (timeless-ctx Γ))) →
                      allnow-ty (timeless-ty T) ≅ᵗʸ T [ to (now-timeless-ctx Γ) ]
func (from (allnow-timeless-tyʳ T)) tm = tm ⟨ 0 , tt ⟩'
_↣_.naturality (from (allnow-timeless-tyʳ T)) = ty-cong T refl
func (to (allnow-timeless-tyʳ T)) t ⟨ _ , _ ⟩' = t
Tm.naturality (func (to (allnow-timeless-tyʳ T)) t) _ _ = strong-ty-id T
_↣_.naturality (to (allnow-timeless-tyʳ T)) = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
eq (isoˡ (allnow-timeless-tyʳ T)) tm = tm-≅-to-≡ (record { eq = λ _ → trans (sym (Tm.naturality tm z≤n refl)) (strong-ty-id T) })
eq (isoʳ (allnow-timeless-tyʳ T)) _ = refl

allnow-timeless : allnow ⓜ timeless ≅ᵐ 𝟙
eq-lock allnow-timeless = now-timeless-ctx
eq-mod-tyʳ allnow-timeless = allnow-timeless-tyʳ

now-timeless-ctx-intro : {A : ClosedTy ★} {{_ : IsClosedNatural A}} {Γ : Ctx ★} →
                         Tm Γ A → Tm (now (timeless-ctx Γ)) A
now-timeless-ctx-intro {A} t = untimeless-tm (unallnow-tm (ι[ eq-mod-closed allnow-timeless A ] t))

to-timeless-now-ctx : (Γ : Ctx ω) → (Γ ⇒ timeless-ctx (now Γ))
func (to-timeless-now-ctx Γ) = Γ ⟪ z≤n ⟫_
_⇒_.naturality (to-timeless-now-ctx Γ) = ctx-comp Γ

to-timeless-now-ctx-natural : {Δ Γ : Ctx ω} (σ : Δ ⇒ Γ) →
                              to-timeless-now-ctx Γ ⊚ σ ≅ˢ ctx-fmap (timeless-ctx-functor ⓕ now-functor) σ ⊚ to-timeless-now-ctx Δ
eq (to-timeless-now-ctx-natural σ) δ = _⇒_.naturality σ

timeless∘allnow≤𝟙 : TwoCell (timeless ⓜ allnow) 𝟙
transf-op (transf timeless∘allnow≤𝟙) = to-timeless-now-ctx
CtxNatTransf.naturality (transf timeless∘allnow≤𝟙) = to-timeless-now-ctx-natural

from-timeless-allnow-ty : {Γ : Ctx ω} {T : Ty (timeless-ctx (now Γ))} →
                          Tm Γ (timeless-ty (allnow-ty T)) → Tm Γ (T [ to-timeless-now-ctx Γ ])
from-timeless-allnow-ty {Γ = Γ} t = unallnow-tm (untimeless-tm t) [ to-timeless-now-ctx Γ ]'
