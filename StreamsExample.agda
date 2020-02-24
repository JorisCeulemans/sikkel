module StreamsExample where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)
open import Level renaming (zero to lzero; suc to lsuc)

open import Helpers
open import CwF-Structure

first-≤ : ∀ {m n} {A : Set ℓ} → m ≤ n → Vec A n → Vec A m
first-≤ z≤n as = []
first-≤ (s≤s ineq) (a ∷ as) = a ∷ first-≤ ineq as

first-≤-refl : ∀ {n} {A : Set ℓ} {as : Vec A n} → first-≤ (≤-refl) as ≡ as
first-≤-refl {n = zero} {as = []} = refl
first-≤-refl {n = suc n} {as = a ∷ as} = cong (a ∷_) first-≤-refl

first-≤-trans : ∀ {k m n} {A : Set ℓ} (k≤m : k ≤ m) (m≤n : m ≤ n) (as : Vec A n) →
                first-≤ (≤-trans k≤m m≤n) as ≡ first-≤ k≤m (first-≤ m≤n as)
first-≤-trans z≤n m≤n as = refl
first-≤-trans (s≤s k≤m) (s≤s m≤n) (a ∷ as) = cong (a ∷_) (first-≤-trans k≤m m≤n as)

Stream : Ty {0ℓ} ◇
type Stream = λ n _ → Vec ℕ n
morph Stream = λ ineq _ → first-≤ ineq
morph-id Stream = λ _ → funext λ xs → first-≤-refl
morph-comp Stream = λ k≤m m≤n _ → funext λ xs → first-≤-trans k≤m m≤n xs
