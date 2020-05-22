module Categories where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Function
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import Helpers

record Category : Set₁ where
  field
    Ob : Set
    Hom : Ob → Ob → Set
    hom-id : ∀ {x} → Hom x x
    _∙_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z

  infixr 9 _∙_

  field
    ∙assoc : ∀ {x y z w} {f : Hom x y} {g : Hom y z} {h : Hom z w} →
            (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    hom-idʳ : ∀ {x y} {f : Hom x y} → f ∙ hom-id ≡ f
    hom-idˡ : ∀ {x y} {f : Hom x y} → hom-id ∙ f ≡ f

category-composition : (C : Category) {x y z : Category.Ob C} →
                       Category.Hom C y z → Category.Hom C x y → Category.Hom C x z
category-composition = Category._∙_

syntax category-composition C g f = g ∙[ C ] f

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

Type-groupoid : (X : Set) → Category
Type-groupoid X = record
                    { Ob = X
                    ; Hom = _≡_
                    ; hom-id = refl
                    ; _∙_ = λ y=z x=y → trans x=y y=z
                    ; ∙assoc = λ {_ _ _ _ x=y _ _} → sym (trans-assoc x=y)
                    ; hom-idʳ = refl
                    ; hom-idˡ = trans-reflʳ _
                    }

record Functor (C D : Category) : Set where
  open Category
  field
    ob : Ob C → Ob D
    hom : ∀ {x y} → Hom C x y → Hom D (ob x) (ob y)
    id-law : ∀ {x} → hom (hom-id C {x}) ≡ hom-id D {ob x}
    comp-law : ∀ {x y z} {f : Hom C x y} {g : Hom C y z} →
               hom (g ∙[ C ] f) ≡ (hom g) ∙[ D ] (hom f)

{-
-- The following definitions are more general (the types of objects and morphisms
-- to live in any universe), but need some reworking of levels in contexts and
-- types to work. We postpone this until a later time.
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

category-composition : ∀ {o h} (C : Category {o}{h}) {x y z : Category.Ob C} →
                       Category.Hom C y z → Category.Hom C x y → Category.Hom C x z
category-composition = Category._∙_

syntax category-composition C g f = g ∙[ C ] f

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

record Functor {o o' h h'} (C : Category {o}{h}) (D : Category {o'}{h'}) : Set (o ⊔ o' ⊔ h ⊔ h') where
  open Category
  field
    ob : Ob C → Ob D
    hom : ∀ {x y} → Hom C x y → Hom D (ob x) (ob y)
    id-law : ∀ {x} → hom (hom-id C {x}) ≡ hom-id D {ob x}
    comp-law : ∀ {x y z} {f : Hom C x y} {g : Hom C y z} →
               hom (g ∙[ C ] f) ≡ (hom g) ∙[ D ] (hom f)
-}
