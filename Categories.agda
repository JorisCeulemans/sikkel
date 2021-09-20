--------------------------------------------------
-- Definition of categories, functors + some examples
--------------------------------------------------

module Categories where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality

open import Helpers

-- Currently, we only have categories with object and morphism types in Set₀.
-- This is sufficient for e.g. guarded recursion, but we will generalize this
-- in the future (it requires some reworking of contexts and types).
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
open Category

category-composition : (C : Category) {x y z : Ob C} →
                       Hom C y z → Hom C x y → Hom C x z
category-composition = _∙_

syntax category-composition C g f = g ∙[ C ] f

Minimal : (C : Category) (x : Category.Ob C) → Set
Minimal C x = ∀ (y : (Σ (Category.Ob C) λ y → Category.Hom C y x)) → y ≡ (x , Category.hom-id C)

ω : Category
Ob ω = ℕ
Hom ω m n = m ≤ n
hom-id ω = ≤-refl
_∙_ ω m≤n k≤m = ≤-trans k≤m m≤n
∙assoc ω = ≤-irrelevant _ _
hom-idʳ ω = ≤-irrelevant _ _
hom-idˡ ω = ≤-irrelevant _ _

★ : Category
Ob ★ = ⊤
Hom ★ _ _ = ⊤
hom-id ★ = tt
_∙_ ★ _ _ = tt
∙assoc ★ = refl
hom-idʳ ★ = refl
hom-idˡ ★ = refl

data 𝟚-Obj : Set where
  type-obj : 𝟚-Obj
  pred-obj : 𝟚-Obj

data 𝟚-Hom : 𝟚-Obj → 𝟚-Obj → Set where
  type-id : 𝟚-Hom type-obj type-obj
  pred-id : 𝟚-Hom pred-obj pred-obj
  type-pred : 𝟚-Hom type-obj pred-obj

𝟚 : Category
Ob 𝟚 = 𝟚-Obj
Hom 𝟚 = 𝟚-Hom
hom-id 𝟚 {type-obj} = type-id
hom-id 𝟚 {pred-obj} = pred-id
_∙_ 𝟚 g type-id = g
_∙_ 𝟚 g pred-id = g
_∙_ 𝟚 pred-id type-pred = type-pred
∙assoc 𝟚 {f = type-id} = refl
∙assoc 𝟚 {f = pred-id} = refl
∙assoc 𝟚 {f = type-pred} {pred-id} = refl
hom-idʳ 𝟚 {x = type-obj} = refl
hom-idʳ 𝟚 {x = pred-obj} = refl
hom-idˡ 𝟚 {f = type-id} = refl
hom-idˡ 𝟚 {f = pred-id} = refl
hom-idˡ 𝟚 {f = type-pred} = refl

data ⋀-Obj : Set where
  left : ⋀-Obj
  right : ⋀-Obj
  relation : ⋀-Obj

data ⋀-Hom : ⋀-Obj → ⋀-Obj → Set where
  left-id     : ⋀-Hom left left
  right-id    : ⋀-Hom right right
  relation-id : ⋀-Hom relation relation
  left-rel    : ⋀-Hom left relation
  right-rel   : ⋀-Hom right relation

⋀ : Category
Ob ⋀ = ⋀-Obj
Hom ⋀ = ⋀-Hom
hom-id ⋀ {left} = left-id
hom-id ⋀ {right} = right-id
hom-id ⋀ {relation} = relation-id
_∙_ ⋀ g left-id = g
_∙_ ⋀ g right-id = g
_∙_ ⋀ g relation-id = g
_∙_ ⋀ relation-id left-rel = left-rel
_∙_ ⋀ relation-id right-rel = right-rel
∙assoc ⋀ {f = left-id} = refl
∙assoc ⋀ {f = right-id} = refl
∙assoc ⋀ {f = relation-id} = refl
∙assoc ⋀ {f = left-rel} {relation-id} = refl
∙assoc ⋀ {f = right-rel} {relation-id} = refl
hom-idʳ ⋀ {left} = refl
hom-idʳ ⋀ {right} = refl
hom-idʳ ⋀ {relation} = refl
hom-idˡ ⋀ {f = left-id} = refl
hom-idˡ ⋀ {f = right-id} = refl
hom-idˡ ⋀ {f = relation-id} = refl
hom-idˡ ⋀ {f = left-rel} = refl
hom-idˡ ⋀ {f = right-rel} = refl

Type-groupoid : (X : Set) → Category
Ob (Type-groupoid X) = X
Hom (Type-groupoid X) = _≡_
hom-id (Type-groupoid X) = refl
_∙_ (Type-groupoid X) y=z x=y = trans x=y y=z
∙assoc (Type-groupoid X) {f = x=y} = sym (trans-assoc x=y)
hom-idʳ (Type-groupoid X) = refl
hom-idˡ (Type-groupoid X) = trans-reflʳ _

record Functor (C D : Category) : Set where
  open Category
  field
    ob : Ob C → Ob D
    hom : ∀ {x y} → Hom C x y → Hom D (ob x) (ob y)
    id-law : ∀ {x} → hom (hom-id C {x}) ≡ hom-id D {ob x}
    comp-law : ∀ {x y z} {f : Hom C x y} {g : Hom C y z} →
               hom (g ∙[ C ] f) ≡ (hom g) ∙[ D ] (hom f)

{-
-- The following definitions are more general (the types of objects and morphisms are allowed
-- to live in any universe), but need some reworking of levels in contexts and types to work.
-- Examples like guarded recursion can be worked out using the definitions above, so we postpone
-- this until some later time.
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

category-composition : ∀ {o h} (C : Category {o}{h}) {x y z : Ob C} →
                       Hom C y z → Hom C x y → Hom C x z
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
