open import Categories

module Types.Universe {C : Category} where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl)

open import CwF-Structure

𝒰 : (ℓ r : Level) → Ty {C = C} ◇ (lsuc ℓ ⊔ lsuc r) (ℓ ⊔ r)
Setoid.Carrier (type (𝒰 ℓ r) x _) = Ty {C = C} (𝕪 x) ℓ r
Setoid._≈_ (type (𝒰 ℓ r) x _) = _≅ᵗʸ_
IsEquivalence.refl (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-refl
IsEquivalence.sym (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-sym
IsEquivalence.trans (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-trans
morph (𝒰 ℓ r) f _ = _[ to-𝕪⇒𝕪 f ]
morph-cong (𝒰 ℓ r) f _ = ty-subst-cong-ty (to-𝕪⇒𝕪 f)
morph-hom-cong (𝒰 ℓ r) ≡-refl = ≅ᵗʸ-refl
morph-id (𝒰 ℓ r) t = ≅ᵗʸ-trans (ty-subst-cong-subst 𝕪-refl t) (ty-subst-id t)
morph-comp (𝒰 ℓ r) f g _ _ t = ≅ᵗʸ-trans (ty-subst-cong-subst (≅ˢ-sym (𝕪-comp f g)) t) (≅ᵗʸ-sym (ty-subst-comp t (to-𝕪⇒𝕪 g) (to-𝕪⇒𝕪 f)))
