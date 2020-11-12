{-# OPTIONS --without-K #-}

--------------------------------------------------
-- The yoneda embedding and yoneda lemma
--------------------------------------------------

open import Categories

module CwF-Structure.Yoneda {C : Category} where

open import Function using (_∘_)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality
  hiding ([_]; naturality) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; setoid to ≡-setoid)

open import Helpers
open import CwF-Structure.Contexts

open Category C

private
  variable
    x y : Ob
    r : Level
    Γ : Ctx C ℓ r


-- Yoneda embedding
𝕪 : Ob → Ctx C 0ℓ 0ℓ
setoid (𝕪 x) y = ≡-setoid (Hom y x)
rel (𝕪 x) f g = g ∙ f
rel-cong (𝕪 x) f = cong (_∙ f)
rel-id (𝕪 x) _ = hom-idʳ
rel-comp (𝕪 x) _ _ _ = ≡-sym ∙assoc

-- The Yoneda lemma
to-𝕪⇒* : Γ ⟨ x ⟩ → 𝕪 x ⇒ Γ
func (to-𝕪⇒* {Γ = Γ} γ) f = Γ ⟪ f ⟫ γ
func-cong (to-𝕪⇒* {Γ = Γ} γ) ≡-refl = ctx≈-refl Γ
naturality (to-𝕪⇒* {Γ = Γ} γ) f = ctx≈-sym Γ (rel-comp Γ _ f γ)

from-𝕪⇒* : 𝕪 x ⇒ Γ → Γ ⟨ x ⟩
from-𝕪⇒* σ = func σ hom-id

𝕪-to-∘-from : (σ : 𝕪 x ⇒ Γ) → to-𝕪⇒* (from-𝕪⇒* σ) ≅ˢ σ
eq (𝕪-to-∘-from {Γ = Γ} σ) f =
  begin
    Γ ⟪ f ⟫ func σ hom-id
  ≈⟨ naturality σ hom-id ⟩
    func σ (hom-id ∙ f)
  ≈⟨ func-cong σ hom-idˡ ⟩
    func σ f ∎
  where open SetoidReasoning (setoid Γ _)

𝕪-from-∘-to : (γ : Γ ⟨ x ⟩) → from-𝕪⇒* {Γ = Γ} (to-𝕪⇒* γ) ≈[ Γ ]≈ γ
𝕪-from-∘-to {Γ = Γ} γ = rel-id Γ γ

-- Proving that the Yoneda embedding is fully faithful
to-𝕪⇒𝕪 : Hom x y → 𝕪 x ⇒ 𝕪 y
to-𝕪⇒𝕪 = to-𝕪⇒*

from-𝕪⇒𝕪 : 𝕪 x ⇒ 𝕪 y → Hom x y
from-𝕪⇒𝕪 = from-𝕪⇒*

𝕪-from-∘-to' : (f : Hom x y) → from-𝕪⇒𝕪 (to-𝕪⇒𝕪 f) ≡ f
𝕪-from-∘-to' f = hom-idʳ

𝕪-to-∘-from' : (σ : 𝕪 x ⇒ 𝕪 y) → to-𝕪⇒𝕪 (from-𝕪⇒𝕪 σ) ≅ˢ σ
𝕪-to-∘-from' σ = 𝕪-to-∘-from σ

-- Functoriality of the Yoneda embedding
𝕪-refl : to-𝕪⇒𝕪 hom-id ≅ˢ id-subst (𝕪 x)
eq 𝕪-refl _ = hom-idˡ

𝕪-comp : (f : Hom x y) (γ : Γ ⟨ y ⟩) → to-𝕪⇒* {Γ = Γ} γ ⊚ to-𝕪⇒𝕪 f ≅ˢ to-𝕪⇒* (Γ ⟪ f ⟫ γ)
eq (𝕪-comp {Γ = Γ} f γ) g = rel-comp Γ g f γ
