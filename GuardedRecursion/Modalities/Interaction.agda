--------------------------------------------------
-- Proofs about the interactions between the different
-- modalities for guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Interaction where

open import Data.Nat
open import Data.Unit
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.Global

private
  variable
    ℓ ℓc ℓt : Level


--------------------------------------------------
-- Interaction between the global and later modalities

earlier-timeless-ctx : {Γ : Ctx ★ ℓ} → ◄ (timeless-ctx Γ) ≅ᶜ timeless-ctx Γ
func (from (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (from (earlier-timeless-ctx {Γ = Γ})) _ = refl
func (to (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (to (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoˡ (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoʳ (earlier-timeless-ctx {Γ = Γ})) _ = refl

global-later-ty : {Γ : Ctx ★ ℓc} (T : Ty (timeless-ctx Γ) ℓt) →
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

global-later'-ty : {Γ : Ctx ★ ℓc} (T : Ty (timeless-ctx Γ) ℓt) →
                   global-ty T ≅ᵗʸ global-ty (▻' T)
global-later'-ty = global-later-ty
