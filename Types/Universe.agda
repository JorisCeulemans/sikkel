module Types.Universe where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.SubstitutionSequence
open import Yoneda

𝓤 : ∀ {ℓ} → Ty (◇ {lsuc ℓ})
type 𝓤 n _ = Ty (𝕪 n)
morph 𝓤 m≤n _ T = T [ to-𝕪⇒𝕪 m≤n ]
morph-id 𝓤 T = trans (cong (T [_]) 𝕪-refl) (ty-subst-id T)
morph-comp 𝓤 k≤m m≤n T = trans (cong (T [_]) (sym (𝕪-comp k≤m (lift m≤n)))) (sym (ty-subst-comp T (to-𝕪⇒𝕪 m≤n) (to-𝕪⇒𝕪 k≤m)))

⌜_⌝ : Ty (◇ {ℓ}) → Tm ◇ (𝓤 {ℓ})
term ⌜ T ⌝ n _ = T [ !◇ (𝕪 n) ]
naturality ⌜ T ⌝ {m = m}{n} m≤n _ = ty-subst-seq-cong (!◇ (𝕪 n) ∷ to-𝕪⇒𝕪 m≤n ◼) (!◇ (𝕪 m) ◼) T (◇-terminal (𝕪 m) _ _)

El : Tm ◇ (𝓤 {ℓ}) → Ty (◇ {ℓ})
type (El T) n _ = (T ⟨ n , _ ⟩') ⟨ n , lift ≤-refl ⟩
morph (El T) m≤n _ t = subst (λ x → x ⟨ _ , lift ≤-refl ⟩) (naturality T m≤n _)
                       (subst (λ x → (T ⟨ _ , _ ⟩') ⟨ _ , lift x ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) (≤-trans ≤-refl m≤n))
                       ((T ⟨ _ , _ ⟩') ⟪ m≤n , lift ≤-refl ⟫ t))
morph-id (El T) {n = n} t = {!!}
morph-comp (El T) = {!!}
