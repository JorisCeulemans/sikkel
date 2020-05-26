module Types.Universe where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.SubstitutionSequence
open import Yoneda

-- This was an attempt to define a universe type using ω as base category.
-- Note that it will not typechek anymore (not even with base category ω) because
-- ty-subst-id and ty-subst-cong do not have the right types (they used to be types
-- expressing propositional equality, but now they only express _≅ᵗʸ_).
-- We leave the development of a universe type for future work, and will first focus
-- on shallowly embedding non-dependent type theories.

{-
𝓤 : ∀ {ℓ} → Ty (◇ {lsuc ℓ})
type 𝓤 n _ = Ty (𝕪 n)
morph 𝓤 m≤n _ T = T [ to-𝕪⇒𝕪 m≤n ]
morph-id 𝓤 T = trans (cong (T [_]) 𝕪-refl) (ty-subst-id T)
morph-comp 𝓤 k≤m m≤n eq-nm eq-mk T = trans (cong (T [_]) (sym (𝕪-comp k≤m (lift m≤n))))
                                             (sym (ty-subst-comp T (to-𝕪⇒𝕪 m≤n) (to-𝕪⇒𝕪 k≤m)))

⌜_⌝ : Ty (◇ {ℓ}) → Tm ◇ (𝓤 {ℓ})
term ⌜ T ⌝ n _ = T [ !◇ (𝕪 n) ]
naturality ⌜ T ⌝ {m = m}{n} m≤n _ = ty-subst-seq-cong (!◇ (𝕪 n) ∷ to-𝕪⇒𝕪 m≤n ◼) (!◇ (𝕪 m) ◼) T (◇-terminal (𝕪 m) _ _)

El : Tm ◇ (𝓤 {ℓ}) → Ty (◇ {ℓ})
type (El T) n _ = (T ⟨ n , _ ⟩') ⟨ n , lift ≤-refl ⟩
morph (El T) {m = m}{n} m≤n _ t = subst (λ x → x ⟨ _ , _ ⟩) (naturality T m≤n refl)
                                  (T ⟨ n , lift tt ⟩' ⟪ m≤n , cong lift (≤-irrelevant _ _) ⟫ t)
morph-id (El T) {n = n} t = {!!}
morph-comp (El T) k≤m m≤n _ _ t = {!!}
-}
