module Categories where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import Helpers

record Category {o h} : Set (lsuc (o ⊔ h)) where
  field
    Ob : Set o
    Hom : Ob → Ob → Set h
    hom-id : ∀ {x} → Hom x x
    _∙_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z

  infixr 9 _∙_

  field
    ∙assoc : ∀ {x y z w} {f : Hom x y} {g : Hom y z} {h : Hom z w} →
            (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    hom-idʳ : ∀ {x y} {f : Hom x y} → f ∙ hom-id ≡ f
    hom-idˡ : ∀ {x y} {f : Hom x y} → hom-id ∙ f ≡ f

ℕ-poset : Category
ℕ-poset = record
             { Ob = ℕ
             ; Hom = λ m n → m ≤ n
             ; hom-id = ≤-refl
             ; _∙_ = λ m≤n k≤m → ≤-trans k≤m m≤n
             ; ∙assoc = ≤-irrelevant _ _
             ; hom-idʳ = ≤-irrelevant _ _
             ; hom-idˡ = ≤-irrelevant _ _
             }

Sets : Category {lsuc ℓ} {ℓ}
Sets {ℓ} = record
             { Ob = Set ℓ
             ; Hom = λ X Y → (X → Y)
             ; hom-id = id
             ; _∙_ = λ g f → g ∘ f
             ; ∙assoc = refl
             ; hom-idʳ = refl
             ; hom-idˡ = refl
             }

Type-groupoid : (X : Set ℓ) → Category
Type-groupoid X = record
                    { Ob = X
                    ; Hom = _≡_
                    ; hom-id = refl
                    ; _∙_ = λ y=z x=y → trans x=y y=z
                    ; ∙assoc = λ {_ _ _ _ x=y _ _} → sym (trans-assoc x=y)
                    ; hom-idʳ = refl
                    ; hom-idˡ = trans-reflʳ _
                    }
