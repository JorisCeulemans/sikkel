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
  ≅⟨ ⊚-congʳ (⊚-congˡ (isoˡ Γ=Θ)) ⟩
    to Δ=Γ ⊚ (id-subst _ ⊚ from Δ=Γ)
  ≅⟨ ⊚-congʳ (id-subst-unitˡ (from Δ=Γ)) ⟩
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
  ≅⟨ ⊚-congʳ (⊚-congˡ (isoʳ Δ=Γ)) ⟩
    from Γ=Θ ⊚ (id-subst _ ⊚ to Γ=Θ)
  ≅⟨ ⊚-congʳ (id-subst-unitˡ (to Γ=Θ)) ⟩
    from Γ=Θ ⊚ to Γ=Θ
  ≅⟨ isoʳ Γ=Θ ⟩
    id-subst _ ∎
  where open ≅ˢ-Reasoning

-- There is no module ≅ᶜ-Reasoning because Ctx C with _≅ᶜ_ is a
-- groupoid and not a setoid. Hence we do not want to add reflᶜ to the
-- end of every proof of type equivalence.
