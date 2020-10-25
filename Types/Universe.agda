open import Categories

module Types.Universe {C : Category} where

open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality
  hiding ([_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import CwF-Structure
open import Reflection.SubstitutionSequence

open Category C

private
  variable
    ℓ r : Level


𝒰 : (ℓ r : Level) → Ty {C = C} ◇ (lsuc ℓ ⊔ lsuc r) (ℓ ⊔ r)
Setoid.Carrier (type (𝒰 ℓ r) x _) = Ty {C = C} (𝕪 x) ℓ r
Setoid._≈_ (type (𝒰 ℓ r) x _) = _≅ᵗʸ_
IsEquivalence.refl (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-refl
IsEquivalence.sym (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-sym
IsEquivalence.trans (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-trans
morph (𝒰 ℓ r) f _ = _[ to-𝕪⇒𝕪 f ]
morph-cong (𝒰 ℓ r) f _ = ty-subst-cong-ty (to-𝕪⇒𝕪 f)
morph-hom-cong (𝒰 ℓ r) ≡-refl = ≅ᵗʸ-refl
morph-id (𝒰 ℓ r) t = ≅ᵗʸ-trans (ty-subst-cong-subst 𝕪-refl t)
                               (ty-subst-id t)
morph-comp (𝒰 ℓ r) f g _ _ t = ≅ᵗʸ-trans (ty-subst-cong-subst (≅ˢ-sym (𝕪-comp f g)) t)
                                         (≅ᵗʸ-sym (ty-subst-comp t (to-𝕪⇒𝕪 g) (to-𝕪⇒𝕪 f)))

⌜_⌝ : Ty {C = C} ◇ ℓ r → Tm ◇ (𝒰 ℓ r)
term ⌜ T ⌝ x _ = T [ !◇ (𝕪 x) ]
Tm.naturality ⌜ T ⌝ {x = x}{y = y} f eγ = ty-subst-seq-cong (!◇ (𝕪 y) ∷ to-𝕪⇒* f ◼) (!◇ (𝕪 x) ◼) T (◇-terminal (𝕪 x) _ _)

El : Tm ◇ (𝒰 ℓ r) → Ty {C = C} ◇ ℓ r
type (El 𝑇) x _ = type (𝑇 ⟨ x , tt ⟩') x hom-id
morph (El 𝑇) {y = y} f _ = func (from (Tm.naturality 𝑇 f ≡-refl)) ∘ (𝑇 ⟨ y , tt ⟩') ⟪ f , ≡-trans hom-idˡ (≡-sym hom-idʳ) ⟫_
morph-cong (El 𝑇) {y = y} f _ = func-cong (from (Tm.naturality 𝑇 f ≡-refl)) ∘ morph-cong (𝑇 ⟨ y , tt ⟩') f _
morph-hom-cong (El 𝑇) {x = x} ≡-refl = ty≈-refl (𝑇 ⟨ x , tt ⟩')
morph-id (El 𝑇) t = {!!}
morph-comp (El 𝑇) = {!!}
