--------------------------------------------------
-- Proofs about the interactions between the different
-- modalities for guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Interaction where

open import Data.Nat
open import Data.Unit
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.AllNow


--------------------------------------------------
-- Interaction between the allnow and later modalities

earlier-timeless-ctx : {Γ : Ctx ★} → ◄ (timeless-ctx Γ) ≅ᶜ timeless-ctx Γ
func (from (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (from (earlier-timeless-ctx {Γ = Γ})) _ = refl
func (to (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (to (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoˡ (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoʳ (earlier-timeless-ctx {Γ = Γ})) _ = refl

allnow-later-ty : {Γ : Ctx ★} {T : Ty (timeless-ctx Γ)} →
                  allnow-ty T ≅ᵗʸ allnow-ty (▻ (T [ from-earlier (timeless-ctx Γ) ]))
func (from allnow-later-ty) t ⟨ zero  , _ ⟩' = _ -- = tt
func (from allnow-later-ty) t ⟨ suc n , _ ⟩' = t ⟨ n , tt ⟩'
Tm.naturality (func (from (allnow-later-ty {T = T})) t) z≤n _ = refl
Tm.naturality (func (from (allnow-later-ty {T = T})) t) (_≤_.s≤s m≤n) _ = trans (ty-cong T refl) (Tm.naturality t m≤n refl)
CwF-Structure.naturality (from (allnow-later-ty {T = T})) t = tm-≅-to-≡ (record { eq =  λ { {zero} _ → refl ; {suc n} _ → ty-cong T refl } })
func (to (allnow-later-ty {T = T})) t ⟨ n , _ ⟩' = t ⟨ suc n , tt ⟩'
Tm.naturality (func (to (allnow-later-ty {T = T})) t) m≤n _ = trans (ty-cong T refl) (Tm.naturality t (_≤_.s≤s m≤n) refl)
CwF-Structure.naturality (to (allnow-later-ty {T = T})) t = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
eq (isoˡ allnow-later-ty) t = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoʳ allnow-later-ty) t = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → refl } })

allnow-later'-ty : {Γ : Ctx ★} {T : Ty (timeless-ctx Γ)} →
                   allnow-ty T ≅ᵗʸ allnow-ty (▻' T)
allnow-later'-ty = allnow-later-ty


--------------------------------------------------
-- Interaction between the allnow and timeless modalities

now-timeless-ctx : {Γ : Ctx ★} → now (timeless-ctx Γ) ≅ᶜ Γ
func (from now-timeless-ctx) = id
_⇒_.naturality (from (now-timeless-ctx {Γ = Γ})) {f = tt} = ctx-id Γ
func (to now-timeless-ctx) = id
_⇒_.naturality (to (now-timeless-ctx {Γ = Γ})) = sym ∘ ctx-id Γ
eq (isoˡ now-timeless-ctx) _ = refl
eq (isoʳ now-timeless-ctx) _ = refl

now-timeless-ctx-intro : {A : ClosedType ★} {{_ : IsClosedNatural A}} {Γ : Ctx ★} →
                         Tm Γ A → Tm (now (timeless-ctx Γ)) A
now-timeless-ctx-intro t = ι⁻¹[ closed-natural (from now-timeless-ctx) ] (t [ from now-timeless-ctx ]')

now-timeless-natural : {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) →
                       from now-timeless-ctx ⊚ now-subst (timeless-subst σ) ≅ˢ σ ⊚ from now-timeless-ctx
eq (now-timeless-natural σ) _ = refl

allnow-timeless-ty : {Γ : Ctx ★} {T : Ty Γ} →
                     allnow-ty (timeless-ty (T [ from now-timeless-ctx ])) ≅ᵗʸ T
func (from allnow-timeless-ty) tm = tm ⟨ 0 , tt ⟩'
CwF-Structure.naturality (from (allnow-timeless-ty {T = T})) _ = ty-cong T refl
func (to allnow-timeless-ty) t ⟨ _ , _ ⟩' = t
Tm.naturality (func (to (allnow-timeless-ty {T = T})) t) _ _ = trans (ty-cong T refl) (ty-id T _)
CwF-Structure.naturality (to (allnow-timeless-ty {T = T})) t = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
eq (isoˡ (allnow-timeless-ty {T = T})) tm = tm-≅-to-≡ (record { eq = λ _ → trans (sym (Tm.naturality tm z≤n refl))
                                                                                 (trans (ty-cong T refl)
                                                                                        (ty-id T _)) })
eq (isoʳ allnow-timeless-ty) _ = refl

to-timeless-now-ctx : (Γ : Ctx ω) → (Γ ⇒ timeless-ctx (now Γ))
func (to-timeless-now-ctx Γ) = Γ ⟪ z≤n ⟫_
_⇒_.naturality (to-timeless-now-ctx Γ) = ctx-comp Γ z≤n _

from-timeless-allnow-ty : {Γ : Ctx ω} {T : Ty (timeless-ctx (now Γ))} →
                          Tm Γ (timeless-ty (allnow-ty T)) → Tm Γ (T [ to-timeless-now-ctx Γ ])
from-timeless-allnow-ty {Γ = Γ} t = unallnow-tm (untimeless-tm t) [ to-timeless-now-ctx Γ ]'
