--------------------------------------------------
-- The yoneda embedding and yoneda lemma
--------------------------------------------------

open import Categories

module Yoneda {C : Category} where

open import Function using (_∘_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts

open Category C

private
  variable
    x y : Ob

-- Yoneda embedding
𝕪 : Ob → Ctx C ℓ
set (𝕪 {ℓ} x) y = Lift ℓ (Hom y x)
rel (𝕪 x) f (lift g) = lift (g ∙ f)
rel-id (𝕪 x) (lift _) = cong lift hom-idʳ
rel-comp (𝕪 x) _ _ (lift _) = cong lift (sym ∙assoc)

𝕪[_]_ : ∀ ℓ → Ob → Ctx C ℓ
𝕪[ ℓ ] x = 𝕪 {ℓ} x

-- The Yoneda lemma
to-𝕪⇒* : {Γ : Ctx C ℓ} → Γ ⟨ x ⟩ → 𝕪[ ℓ ] x ⇒ Γ
func (to-𝕪⇒* {Γ = Γ} γ) (lift f) = Γ ⟪ f ⟫ γ
naturality (to-𝕪⇒* {Γ = Γ} γ) (lift f) = sym (rel-comp Γ _ f γ)

from-𝕪⇒* : {Γ : Ctx C ℓ} → 𝕪[ ℓ ] x ⇒ Γ → Γ ⟨ x ⟩
from-𝕪⇒* σ = func σ (lift hom-id)

𝕪-to-∘-from : {Γ : Ctx C ℓ} (σ : 𝕪[ ℓ ] x ⇒ Γ) → to-𝕪⇒* (from-𝕪⇒* σ) ≅ˢ σ
eq (𝕪-to-∘-from σ) (lift f) = trans (naturality σ (lift hom-id))
                                    (cong (func σ ∘ lift) hom-idˡ)

𝕪-from-∘-to : {Γ : Ctx C ℓ} (γ : Γ ⟨ x ⟩) → from-𝕪⇒* {ℓ = ℓ} {Γ = Γ} (to-𝕪⇒* γ) ≡ γ
𝕪-from-∘-to {Γ = Γ} γ = rel-id Γ γ

-- Proving that the Yoneda embedding is fully faithful
to-𝕪⇒𝕪 : Hom x y → 𝕪[ ℓ ] x ⇒ 𝕪[ ℓ ] y
to-𝕪⇒𝕪 = to-𝕪⇒* ∘ lift

from-𝕪⇒𝕪 : 𝕪[ ℓ ] x ⇒ 𝕪[ ℓ ] y → Hom x y
from-𝕪⇒𝕪 = lower ∘ from-𝕪⇒*

𝕪-from-∘-to' : (f : Hom x y) → from-𝕪⇒𝕪 (to-𝕪⇒𝕪 {ℓ = ℓ} f) ≡ f
𝕪-from-∘-to' f = hom-idʳ

𝕪-to-∘-from' : (σ : 𝕪[ ℓ ] x ⇒ 𝕪 y) → to-𝕪⇒𝕪 (from-𝕪⇒𝕪 σ) ≅ˢ σ
𝕪-to-∘-from' σ = 𝕪-to-∘-from σ

-- Functoriality of the Yoneda embedding
𝕪-refl : to-𝕪⇒𝕪 hom-id ≅ˢ id-subst (𝕪[ ℓ ] x)
eq 𝕪-refl (lift _) = cong lift hom-idˡ

𝕪-comp : {Γ : Ctx C ℓ} (f : Hom x y) (γ : Γ ⟨ y ⟩) → to-𝕪⇒* {ℓ = ℓ} {Γ = Γ} γ ⊚ to-𝕪⇒𝕪 f ≅ˢ to-𝕪⇒* (Γ ⟪ f ⟫ γ)
eq (𝕪-comp {Γ = Γ} f γ) (lift g) = rel-comp Γ g f γ
