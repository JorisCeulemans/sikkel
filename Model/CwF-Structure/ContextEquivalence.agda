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

reflᶜ : Γ ≅ᶜ Γ
from (reflᶜ {Γ = Γ}) = id-subst Γ
to (reflᶜ {Γ = Γ}) = id-subst Γ
eq (isoˡ reflᶜ) _ = refl
eq (isoʳ reflᶜ) _ = refl

symᶜ : Δ ≅ᶜ Γ → Γ ≅ᶜ Δ
from (symᶜ Δ=Γ) = to Δ=Γ
to (symᶜ Δ=Γ) = from Δ=Γ
isoˡ (symᶜ Δ=Γ) = isoʳ Δ=Γ
isoʳ (symᶜ Δ=Γ) = isoˡ Δ=Γ

transᶜ : Δ ≅ᶜ Γ → Γ ≅ᶜ Θ → Δ ≅ᶜ Θ
from (transᶜ Δ=Γ Γ=Θ) = from Γ=Θ ⊚ from Δ=Γ
to (transᶜ Δ=Γ Γ=Θ) = to Δ=Γ ⊚ to Γ=Θ
isoˡ (transᶜ Δ=Γ Γ=Θ) =
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
isoʳ (transᶜ Δ=Γ Γ=Θ) =
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
  step-≅ _ Δ≅Θ Γ≅Δ = transᶜ Γ≅Δ Δ≅Θ

  step-≅˘ : (Γ : Ctx C) → Δ ≅ᶜ Θ → Δ ≅ᶜ Γ → Γ ≅ᶜ Θ
  step-≅˘ _ Δ≅Θ Δ≅Γ = transᶜ (symᶜ Δ≅Γ) Δ≅Θ

  _∎ : (Γ : Ctx C) → Γ ≅ᶜ Γ
  _∎ _ = reflᶜ

  syntax step-≅  Γ Δ≅Θ Γ≅Δ = Γ ≅⟨  Γ≅Δ ⟩ Δ≅Θ
  syntax step-≅˘ Γ Δ≅Θ Δ≅Γ = Γ ≅˘⟨ Δ≅Γ ⟩ Δ≅Θ
