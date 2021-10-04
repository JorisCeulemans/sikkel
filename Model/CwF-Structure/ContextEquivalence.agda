--------------------------------------------------
-- Equivalence of contexts
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.ContextEquivalence {C : BaseCategory} where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Reflection.Substitution

infix 1 _≅ᶜ_

private
  variable
    Γ Δ Θ : Ctx C

-- Two contexts are equivalent if they are naturally equivalent as presheaves.
record _≅ᶜ_ (Δ : Ctx C) (Γ : Ctx C) : Set where
  field
    from : Δ ⇒ Γ
    to : Γ ⇒ Δ
    isoˡ : to ⊚ from ≅ˢ id-subst Δ
    isoʳ : from ⊚ to ≅ˢ id-subst Γ
open _≅ᶜ_ public

≅ᶜ-refl : Γ ≅ᶜ Γ
from (≅ᶜ-refl {Γ = Γ}) = id-subst Γ
to (≅ᶜ-refl {Γ = Γ}) = id-subst Γ
eq (isoˡ ≅ᶜ-refl) _ = refl
eq (isoʳ ≅ᶜ-refl) _ = refl

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
  ≅⟨ ⊚-congˡ (⊚-congʳ (isoˡ Γ=Θ)) ⟩
    to Δ=Γ ⊚ (id-subst _ ⊚ from Δ=Γ)
  ≅⟨ ⊚-congˡ (⊚-id-substˡ (from Δ=Γ)) ⟩
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
  ≅⟨ ⊚-congˡ (⊚-congʳ (isoʳ Δ=Γ)) ⟩
    from Γ=Θ ⊚ (id-subst _ ⊚ to Γ=Θ)
  ≅⟨ ⊚-congˡ (⊚-id-substˡ (to Γ=Θ)) ⟩
    from Γ=Θ ⊚ to Γ=Θ
  ≅⟨ isoʳ Γ=Θ ⟩
    id-subst _ ∎
  where open ≅ˢ-Reasoning

module ≅ᶜ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : Γ ≅ᶜ Δ → Γ ≅ᶜ Δ
  begin_ Γ=Δ = Γ=Δ

  _≅⟨⟩_ : (Γ : Ctx C) → Γ ≅ᶜ Δ → Γ ≅ᶜ Δ
  _ ≅⟨⟩ Γ=Δ = Γ=Δ

  step-≅ : (Γ : Ctx C) → Δ ≅ᶜ Θ → Γ ≅ᶜ Δ → Γ ≅ᶜ Θ
  step-≅ _ Δ≅Θ Γ≅Δ = ≅ᶜ-trans Γ≅Δ Δ≅Θ

  step-≅˘ : (Γ : Ctx C) → Δ ≅ᶜ Θ → Δ ≅ᶜ Γ → Γ ≅ᶜ Θ
  step-≅˘ _ Δ≅Θ Δ≅Γ = ≅ᶜ-trans (≅ᶜ-sym Δ≅Γ) Δ≅Θ

  _∎ : (Γ : Ctx C) → Γ ≅ᶜ Γ
  _∎ _ = ≅ᶜ-refl

  syntax step-≅  Γ Δ≅Θ Γ≅Δ = Γ ≅⟨  Γ≅Δ ⟩ Δ≅Θ
  syntax step-≅˘ Γ Δ≅Θ Δ≅Γ = Γ ≅˘⟨ Δ≅Γ ⟩ Δ≅Θ
