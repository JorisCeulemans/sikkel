--------------------------------------------------
-- Proofs about the interactions between the different
-- modalities for guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Interaction where

open import Data.Nat
open import Data.Unit
open import Function using (id; _∘_)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.Global

private
  variable
    ℓ ℓ' ℓc ℓt : Level


--------------------------------------------------
-- Interaction between the global and later modalities

earlier-timeless-ctx : {Γ : Ctx ★} → ◄ (timeless-ctx Γ) ≅ᶜ timeless-ctx Γ
func (from (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (from (earlier-timeless-ctx {Γ = Γ})) _ = refl
func (to (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (to (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoˡ (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoʳ (earlier-timeless-ctx {Γ = Γ})) _ = refl

global-later-ty : {Γ : Ctx ★} (T : Ty (timeless-ctx Γ)) →
                  global-ty T ≅ᵗʸ global-ty (▻ (T [ from-earlier (timeless-ctx Γ) ]))
term (func (from (global-later-ty T)) t) zero _ = _ -- = tt
term (func (from (global-later-ty T)) t) (suc n) _ = t ⟨ n , tt ⟩'
Tm.naturality (func (from (global-later-ty T)) t) z≤n _ = refl
Tm.naturality (func (from (global-later-ty T)) t) (_≤_.s≤s m≤n) _ = trans (morph-cong T refl) (Tm.naturality t m≤n refl)
CwF-Structure.naturality (from (global-later-ty T)) t = tm-≅-to-≡ (record { eq =  λ { {zero} _ → refl ; {suc n} _ → morph-cong T refl } })
term (func (to (global-later-ty T)) t) n _ = t ⟨ suc n , tt ⟩'
Tm.naturality (func (to (global-later-ty T)) t) m≤n _ = trans (morph-cong T refl) (Tm.naturality t (_≤_.s≤s m≤n) refl)
CwF-Structure.naturality (to (global-later-ty T)) t = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
eq (isoˡ (global-later-ty T)) t = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoʳ (global-later-ty T)) t = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → refl } })

global-later'-ty : {Γ : Ctx ★} (T : Ty (timeless-ctx Γ)) →
                   global-ty T ≅ᵗʸ global-ty (▻' T)
global-later'-ty = global-later-ty


--------------------------------------------------
-- Interaction between the global and timeless modalities

now-timeless-ctx : {Γ : Ctx ★} → now (timeless-ctx Γ) ≅ᶜ Γ
func (from now-timeless-ctx) = id
_⇒_.naturality (from (now-timeless-ctx {Γ = Γ})) {f = tt} = rel-id Γ
func (to now-timeless-ctx) = id
_⇒_.naturality (to (now-timeless-ctx {Γ = Γ})) = sym ∘ rel-id Γ
eq (isoˡ now-timeless-ctx) _ = refl
eq (isoʳ now-timeless-ctx) _ = refl

now-timeless-natural : {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) →
                       from now-timeless-ctx ⊚ now-subst (timeless-subst σ) ≅ˢ σ ⊚ from now-timeless-ctx
eq (now-timeless-natural σ) _ = refl

global-timeless-ty : {Γ : Ctx ★} (T : Ty Γ) →
                     global-ty (timeless-ty (T [ from now-timeless-ctx ])) ≅ᵗʸ T
func (from (global-timeless-ty T)) tm = tm ⟨ 0 , tt ⟩'
CwF-Structure.naturality (from (global-timeless-ty T)) _ = morph-cong T refl
term (func (to (global-timeless-ty T)) t) _ _ = t
Tm.naturality (func (to (global-timeless-ty T)) t) _ _ = trans (morph-cong T refl) (morph-id T _)
CwF-Structure.naturality (to (global-timeless-ty T)) t = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
eq (isoˡ (global-timeless-ty T)) tm = tm-≅-to-≡ (record { eq = λ _ → trans (sym (Tm.naturality tm z≤n refl))
                                                                            (trans (morph-cong T refl)
                                                                                   (morph-id T _)) })
eq (isoʳ (global-timeless-ty T)) _ = refl
