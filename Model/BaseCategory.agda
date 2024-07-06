--------------------------------------------------
-- Definition of base categories, functors + some examples
--------------------------------------------------

module Model.BaseCategory where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding (naturality)

open import Model.Helpers

-- We only support small base categories with object and morphism types in Set₀.
-- This is sufficient for the current applications like guarded recursion.
record BaseCategory : Set₁ where
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
open BaseCategory

category-composition : (C : BaseCategory) {x y z : Ob C} →
                       Hom C y z → Hom C x y → Hom C x z
category-composition = _∙_

syntax category-composition C g f = g ∙[ C ] f

ω : BaseCategory
Ob ω = ℕ
Hom ω m n = m ≤ n
hom-id ω = ≤-refl
_∙_ ω m≤n k≤m = ≤-trans k≤m m≤n
∙assoc ω = ≤-irrelevant _ _
hom-idʳ ω = ≤-irrelevant _ _
hom-idˡ ω = ≤-irrelevant _ _

★ : BaseCategory
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

𝟚 : BaseCategory
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

⋀ : BaseCategory
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

Type-groupoid : (X : Set) → BaseCategory
Ob (Type-groupoid X) = X
Hom (Type-groupoid X) = _≡_
hom-id (Type-groupoid X) = refl
_∙_ (Type-groupoid X) y=z x=y = trans x=y y=z
∙assoc (Type-groupoid X) {f = x=y} = sym (trans-assoc x=y)
hom-idʳ (Type-groupoid X) = refl
hom-idˡ (Type-groupoid X) = trans-reflʳ _

record BaseFunctor (C D : BaseCategory) : Set where
  open BaseCategory
  field
    ob : Ob C → Ob D
    hom : ∀ {x y} → Hom C x y → Hom D (ob x) (ob y)
    id-law : ∀ {x} → hom (hom-id C {x}) ≡ hom-id D {ob x}
    comp-law : ∀ {x y z} {f : Hom C x y} {g : Hom C y z} →
               hom (g ∙[ C ] f) ≡ (hom g) ∙[ D ] (hom f)

open BaseFunctor

id-base-functor : {C : BaseCategory} → BaseFunctor C C
ob id-base-functor x = x
hom id-base-functor f = f
id-law id-base-functor = refl
comp-law id-base-functor = refl

base-functor-comp : {C D E : BaseCategory} →
                    BaseFunctor D E → BaseFunctor C D → BaseFunctor C E
ob (base-functor-comp G F) x = ob G (ob F x)
hom (base-functor-comp G F) f = hom G (hom F f)
id-law (base-functor-comp G F) = trans (cong (hom G) (id-law F)) (id-law G)
comp-law (base-functor-comp G F) = trans (cong (hom G) (comp-law F)) (comp-law G)


record BaseNatTransf {C D : BaseCategory} (F G : BaseFunctor C D) : Set where
  open BaseCategory
  open BaseFunctor

  field
    transf-op : (x : Ob C) → Hom D (ob F x) (ob G x)
    naturality : {x y : Ob C} (f : Hom C x y) →
                 transf-op y ∙[ D ] hom F f ≡ hom G f ∙[ D ] transf-op x

open BaseNatTransf

module _ {C D : BaseCategory} where
  id-base-transf : {F : BaseFunctor C D} → BaseNatTransf F F
  transf-op id-base-transf x = hom-id D
  naturality id-base-transf f = trans (hom-idˡ D) (sym (hom-idʳ D))

  _ⓑ-vert_ : {F G H : BaseFunctor C D} →
             BaseNatTransf G H → BaseNatTransf F G → BaseNatTransf F H
  transf-op (β ⓑ-vert α) x = transf-op β x ∙[ D ] transf-op α x
  naturality (β ⓑ-vert α) f =
    trans (∙assoc D) (
    trans (cong (λ z → transf-op β _ ∙[ D ] z) (naturality α f)) (
    trans (sym (∙assoc D)) (
    trans (cong (λ z → z ∙[ D ] transf-op α _) (naturality β f)) (
    ∙assoc D))))


record _≅ᵇᵗ_ {C D : BaseCategory} {F G : BaseFunctor C D} (α β : BaseNatTransf F G) : Set where
  open BaseCategory
  open BaseNatTransf

  field
    transf-op-eq : (x : Ob C) → transf-op α x ≡ transf-op β x

open _≅ᵇᵗ_


module _ {C D : BaseCategory} {F G : BaseFunctor C D} where
  reflᵇᵗ : {α : BaseNatTransf F G} → α ≅ᵇᵗ α
  transf-op-eq reflᵇᵗ _ = refl

  symᵇᵗ : {α β : BaseNatTransf F G} → α ≅ᵇᵗ β → β ≅ᵇᵗ α
  transf-op-eq (symᵇᵗ 𝓮) x = sym (transf-op-eq 𝓮 x)

  transᵇᵗ : {α1 α2 α3 : BaseNatTransf F G} → α1 ≅ᵇᵗ α2 → α2 ≅ᵇᵗ α3 → α1 ≅ᵇᵗ α3
  transf-op-eq (transᵇᵗ 𝓮 𝓮') x = trans (transf-op-eq 𝓮 x) (transf-op-eq 𝓮' x)
