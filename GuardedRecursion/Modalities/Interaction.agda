--------------------------------------------------
-- Proofs about the interactions between the different
-- modalities for guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Interaction where

open import Data.Nat
open import Data.Unit
import Data.Unit.Polymorphic as Polymorphic
open import Function using (id; _∘_)
open import Level renaming (suc to lsuc)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.Global

private
  variable
    ℓ ℓ' ℓc ℓt r r' rc rt : Level


--------------------------------------------------
-- Interaction between the global and later modalities

earlier-timeless-ctx : {Γ : Ctx ★ ℓ r} → ◄ (timeless-ctx Γ) ≅ᶜ timeless-ctx Γ
from (earlier-timeless-ctx {Γ = Γ}) = from-earlier (timeless-ctx Γ)
func (to (earlier-timeless-ctx {Γ = Γ})) γ = γ
func-cong (to (earlier-timeless-ctx {Γ = Γ})) e = e
_⇒_.naturality (to (earlier-timeless-ctx {Γ = Γ})) _ = ctx≈-refl Γ
eq (isoˡ (earlier-timeless-ctx {Γ = Γ})) _ = ctx≈-refl Γ
eq (isoʳ (earlier-timeless-ctx {Γ = Γ})) _ = ctx≈-refl Γ

global-later-ty : {Γ : Ctx ★ ℓc rc} (T : Ty (timeless-ctx Γ) ℓt rt) →
                  global-ty T ≅ᵗʸ global-ty (▻ (ιc[ earlier-timeless-ctx ] T))
term (func (from (global-later-ty T)) t)  zero   _ = Polymorphic.tt
term (func (from (global-later-ty T)) t) (suc n) _ = t ⟨ n , tt ⟩'
Tm.naturality (func (from (global-later-ty T)) t)  z≤n      _ = Polymorphic.tt
Tm.naturality (func (from (global-later-ty T)) t) (s≤s m≤n) _ = ty≈-trans T (morph-hom-cong T refl) (Tm.naturality t m≤n refl)
eq (func-cong (from (global-later-ty T)) et) {x = zero}  _ = Polymorphic.tt
eq (func-cong (from (global-later-ty T)) et) {x = suc x} _ = eq et tt
eq (CwF-Structure.naturality (from (global-later-ty T)) t) {x = zero}  _ = Polymorphic.tt
eq (CwF-Structure.naturality (from (global-later-ty T)) t) {x = suc x} _ = morph-hom-cong T refl
term (func (to (global-later-ty T)) t) n _ = t ⟨ suc n , tt ⟩'
Tm.naturality (func (to (global-later-ty T)) t) m≤n _ = ty≈-trans T (morph-hom-cong T refl) (Tm.naturality t (s≤s m≤n) refl)
eq (func-cong (to (global-later-ty T)) et) {x = n} _ = eq et {suc n} tt
eq (CwF-Structure.naturality (to (global-later-ty T)) t) _ = morph-hom-cong T refl
eq (eq (isoˡ (global-later-ty T)) t) _ = ty≈-refl T
eq (eq (isoʳ (global-later-ty T)) t) {x = zero}  _ = Polymorphic.tt
eq (eq (isoʳ (global-later-ty T)) t) {x = suc x} _ = ty≈-refl T

global-later'-ty : {Γ : Ctx ★ ℓc rc} (T : Ty (timeless-ctx Γ) ℓt rt) →
                   global-ty T ≅ᵗʸ global-ty (▻' T)
global-later'-ty = global-later-ty


--------------------------------------------------
-- Interaction between the global and timeless modalities

now-timeless-ctx : {Γ : Ctx ★ ℓc rc} → now (timeless-ctx Γ) ≅ᶜ Γ
func (from now-timeless-ctx) = id
func-cong (from now-timeless-ctx) = id
_⇒_.naturality (from (now-timeless-ctx {Γ = Γ})) = rel-id Γ
func (to now-timeless-ctx) = id
func-cong (to now-timeless-ctx) = id
_⇒_.naturality (to (now-timeless-ctx {Γ = Γ})) = ctx≈-sym Γ ∘ rel-id Γ
eq (isoˡ (now-timeless-ctx {Γ = Γ})) _ = ctx≈-refl Γ
eq (isoʳ (now-timeless-ctx {Γ = Γ})) _ = ctx≈-refl Γ

now-timeless-natural : {Δ : Ctx ★ ℓ r} {Γ : Ctx ★ ℓ' r'} (σ : Δ ⇒ Γ) →
                       from now-timeless-ctx ⊚ now-subst (timeless-subst σ) ≅ˢ σ ⊚ from now-timeless-ctx
eq (now-timeless-natural {Γ = Γ} σ) _ = ctx≈-refl Γ

global-timeless-ty : {Γ : Ctx ★ ℓc rc} (T : Ty Γ ℓt rt) →
                     global-ty (timeless-ty (ιc[ now-timeless-ctx ] T)) ≅ᵗʸ T
func (from (global-timeless-ty T)) tm = tm ⟨ 0 , tt ⟩'
func-cong (from (global-timeless-ty T)) e-tm = eq e-tm tt
CwF-Structure.naturality (from (global-timeless-ty T)) _ = morph-hom-cong T refl
term (func (to (global-timeless-ty T)) t) _ _ = t
Tm.naturality (func (to (global-timeless-ty T)) t) _ _ = ty≈-trans T (morph-hom-cong T refl) (morph-id T t)
eq (func-cong (to (global-timeless-ty T)) et) _ = et
eq (CwF-Structure.naturality (to (global-timeless-ty T)) t) _ = morph-hom-cong T refl
eq (eq (isoˡ (global-timeless-ty T)) tm) {x = n} _ =
  begin
    tm ⟨ 0 , tt ⟩'
  ≈˘⟨ Tm.naturality tm z≤n refl ⟩
    T ⟪ tt , _ ⟫ tm ⟨ n , tt ⟩'
  ≈⟨ morph-hom-cong T refl ⟩
    T ⟪ tt , _ ⟫ tm ⟨ n , tt ⟩'
  ≈⟨ morph-id T _ ⟩
    tm ⟨ n , tt ⟩' ∎
  where open SetoidReasoning (type T tt _)
eq (isoʳ (global-timeless-ty T)) _ = ty≈-refl T

to-timeless-now-ctx : (Γ : Ctx ω ℓ r) → Γ ⇒ timeless-ctx (now Γ)
func (to-timeless-now-ctx Γ) = Γ ⟪ z≤n ⟫_
func-cong (to-timeless-now-ctx Γ) = rel-cong Γ z≤n
_⇒_.naturality (to-timeless-now-ctx Γ) = rel-comp Γ z≤n _

from-timeless-global-ty : {Γ : Ctx ω ℓc rc} {T : Ty (timeless-ctx (now Γ)) ℓt rt} →
                          Tm Γ (timeless-ty (global-ty T)) → Tm Γ (T [ to-timeless-now-ctx Γ ])
from-timeless-global-ty {Γ = Γ} t = unglobal-tm (untimeless-tm t) [ to-timeless-now-ctx Γ ]'
