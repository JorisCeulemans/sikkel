{-# OPTIONS --without-K #-}

--------------------------------------------------
-- Equivalence of contexts
--------------------------------------------------

open import Categories

module CwF-Structure.ContextEquivalence {C : Category} where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CwF-Structure.Contexts
open import Reflection.Helpers
open import Reflection.Substitutions

infix 1 _≅ᶜ_

private
  variable
    ℓ ℓ' : Level
    Γ Δ Θ : Ctx C ℓ

-- Two contexts are equivalent if they are naturally equivalent as presheaves.
record _≅ᶜ_ (Δ : Ctx C ℓ) (Γ : Ctx C ℓ') : Set (ℓ ⊔ ℓ') where
  field
    from : Δ ⇒ Γ
    to : Γ ⇒ Δ
    isoˡ : to ⊚ from ≅ˢ id-subst Δ
    isoʳ : from ⊚ to ≅ˢ id-subst Γ
open _≅ᶜ_ public

≅ᶜ-refl : Γ ≅ᶜ Γ
from (≅ᶜ-refl {Γ = Γ}) = id-subst Γ
to (≅ᶜ-refl {Γ = Γ}) = id-subst Γ
eq (isoˡ (≅ᶜ-refl {Γ = Γ})) _ = ctx≈-refl Γ
eq (isoʳ (≅ᶜ-refl {Γ = Γ})) _ = ctx≈-refl Γ

≅ᶜ-sym : Δ ≅ᶜ Γ → Γ ≅ᶜ Δ
from (≅ᶜ-sym Δ=Γ) = to Δ=Γ
to (≅ᶜ-sym Δ=Γ) = from Δ=Γ
isoˡ (≅ᶜ-sym Δ=Γ) = isoʳ Δ=Γ
isoʳ (≅ᶜ-sym Δ=Γ) = isoˡ Δ=Γ

≅ᶜ-trans : Δ ≅ᶜ Γ → Γ ≅ᶜ Θ → Δ ≅ᶜ Θ
from (≅ᶜ-trans Δ=Γ Γ=Θ) = from Γ=Θ ⊚ from Δ=Γ
to (≅ᶜ-trans Δ=Γ Γ=Θ) = to Δ=Γ ⊚ to Γ=Θ
isoˡ (≅ᶜ-trans Δ=Γ Γ=Θ) =
  begin
    (to Δ=Γ ⊚ to Γ=Θ) ⊚ (from Γ=Θ ⊚ from Δ=Γ)
  ≅⟨ subst-reflect ((val (var (to Δ=Γ)) ⊚' val (var (to Γ=Θ))) ⊚' (val (var (from Γ=Θ)) ⊚' val (var (from Δ=Γ))))
                   (val (var (to Δ=Γ)) ⊚' ((val (var (to Γ=Θ)) ⊚' val (var (from Γ=Θ))) ⊚' val (var (from Δ=Γ))))
                   refl ⟩
    to Δ=Γ ⊚ ((to Γ=Θ ⊚ from Γ=Θ) ⊚ from Δ=Γ)
  ≅⟨ ⊚-congˡ (to Δ=Γ) (⊚-congʳ (from Δ=Γ) (isoˡ Γ=Θ)) ⟩
    to Δ=Γ ⊚ (id-subst _ ⊚ from Δ=Γ)
  ≅⟨ ⊚-congˡ (to Δ=Γ) (⊚-id-substˡ (from Δ=Γ)) ⟩
    to Δ=Γ ⊚ from Δ=Γ
  ≅⟨ isoˡ Δ=Γ ⟩
    id-subst _ ∎
  where open ≅ˢ-Reasoning
isoʳ (≅ᶜ-trans Δ=Γ Γ=Θ) =
  begin
    (from Γ=Θ ⊚ from Δ=Γ) ⊚ (to Δ=Γ ⊚ to Γ=Θ)
  ≅⟨ subst-reflect ((val (var (from Γ=Θ)) ⊚' val (var (from Δ=Γ))) ⊚' (val (var (to Δ=Γ)) ⊚' val (var (to Γ=Θ))))
                   (val (var (from Γ=Θ)) ⊚' ((val (var (from Δ=Γ)) ⊚' val (var (to Δ=Γ))) ⊚' val (var (to Γ=Θ))))
                   refl ⟩
    from Γ=Θ ⊚ ((from Δ=Γ ⊚ to Δ=Γ) ⊚ to Γ=Θ)
  ≅⟨ ⊚-congˡ (from Γ=Θ) (⊚-congʳ (to Γ=Θ) (isoʳ Δ=Γ)) ⟩
    from Γ=Θ ⊚ (id-subst _ ⊚ to Γ=Θ)
  ≅⟨ ⊚-congˡ (from Γ=Θ) (⊚-id-substˡ (to Γ=Θ)) ⟩
    from Γ=Θ ⊚ to Γ=Θ
  ≅⟨ isoʳ Γ=Θ ⟩
    id-subst _ ∎
  where open ≅ˢ-Reasoning
