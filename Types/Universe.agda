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
    Γ Δ : Ctx C ℓ r


module OnlyPropElimination where
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

  {-
  El : Tm ◇ (𝒰 ℓ r) → Ty {C = C} ◇ ℓ r
  type (El 𝑇) x _ = type (𝑇 ⟨ x , tt ⟩') x hom-id
  morph (El 𝑇) {y = y} f _ = func (from (Tm.naturality 𝑇 f ≡-refl)) ∘ (𝑇 ⟨ y , tt ⟩') ⟪ f , ≡-trans hom-idˡ (≡-sym hom-idʳ) ⟫_
  morph-cong (El 𝑇) {y = y} f _ = func-cong (from (Tm.naturality 𝑇 f ≡-refl)) ∘ morph-cong (𝑇 ⟨ y , tt ⟩') f _
  morph-hom-cong (El 𝑇) {x = x} ≡-refl = ty≈-refl (𝑇 ⟨ x , tt ⟩')
  morph-id (El 𝑇) t = {!!}
  morph-comp (El 𝑇) = {!!}
  -}

  El : Tm ◇ (𝒰 ℓ r) → Ty {C = C} ◇ ℓ r
  Setoid.Carrier (type (El 𝑇) x _) = Setoid.Carrier (type (𝑇 ⟨ x , tt ⟩') x hom-id)
  Setoid._≈_ (type (El 𝑇) x _) _ _ = Lift _ ⊤
  IsEquivalence.refl (Setoid.isEquivalence (type (El 𝑇) x _)) = lift tt
  IsEquivalence.sym (Setoid.isEquivalence (type (El 𝑇) x _)) = Function.id
  IsEquivalence.trans (Setoid.isEquivalence (type (El 𝑇) x _)) _ _ = lift tt
  morph (El 𝑇) {y = y} f _ = func (from (Tm.naturality 𝑇 f ≡-refl)) ∘ (𝑇 ⟨ y , tt ⟩') ⟪ f , ≡-trans hom-idˡ (≡-sym hom-idʳ) ⟫_
  morph-cong (El 𝑇) _ _ _ = lift tt
  morph-hom-cong (El 𝑇) _ = lift tt
  morph-id (El 𝑇) _ = lift tt
  morph-comp (El 𝑇) _ _ _ _ _ = lift tt


module RestrictToHSets where
  Is-agda-h-prop : Set ℓ → Set ℓ
  Is-agda-h-prop A = (x y : A) → x ≡ y
  
  Is-sikkel-h-set : Ty Γ ℓ r → Set _
  Is-sikkel-h-set {Γ = Γ} T = {x : Ob} {γ : Γ ⟨ x ⟩} (t s : T ⟨ x , γ ⟩) → Is-agda-h-prop (t ≈⟦ T ⟧≈ s)

  []-preserves-setness : (T : Ty Γ ℓ r) (σ : Δ ⇒ Γ) → Is-sikkel-h-set T → Is-sikkel-h-set (T [ σ ])
  []-preserves-setness T σ T-set = T-set

  record Sikkel-h-set {Γℓ Γr} (Γ : Ctx C Γℓ Γr) (ℓ r : Level) : Set (lsuc ℓ ⊔ lsuc r ⊔ Γℓ ⊔ Γr) where
    constructor _,s_
    field
      h-set-type : Ty Γ ℓ r
      h-set-is-h-set : Is-sikkel-h-set h-set-type
  open Sikkel-h-set

  𝒰 : (ℓ r : Level) → Ty {C = C} ◇ (lsuc ℓ ⊔ lsuc r) (ℓ ⊔ r)
  Setoid.Carrier (type (𝒰 ℓ r) x _) = Sikkel-h-set (𝕪 x) ℓ r
  Setoid._≈_ (type (𝒰 ℓ r) x _) (T ,s T-is-set) (S ,s S-is-set) = T ≅ᵗʸ S
  IsEquivalence.refl (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-refl
  IsEquivalence.sym (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-sym
  IsEquivalence.trans (Setoid.isEquivalence (type (𝒰 ℓ r) x _)) = ≅ᵗʸ-trans
  morph (𝒰 ℓ r) f _ (T ,s T-is-set) = (T [ to-𝕪⇒𝕪 f ]) ,s []-preserves-setness T (to-𝕪⇒𝕪 f) T-is-set
  morph-cong (𝒰 ℓ r) f _ = ty-subst-cong-ty _
  morph-hom-cong (𝒰 ℓ r) ≡-refl = ≅ᵗʸ-refl
  morph-id (𝒰 ℓ r) (𝑇 ,s _) = ≅ᵗʸ-trans (ty-subst-cong-subst 𝕪-refl 𝑇) (ty-subst-id 𝑇)
  morph-comp (𝒰 ℓ r) f g _ _ (𝑇 ,s _) = ≅ᵗʸ-trans (ty-subst-cong-subst (≅ˢ-sym (𝕪-comp f g)) 𝑇) (≅ᵗʸ-sym (ty-subst-comp 𝑇 _ _))

  ⌜_,_⌝ : (T : Ty {C = C} ◇ ℓ r) → Is-sikkel-h-set T → Tm ◇ (𝒰 ℓ r)
  term ⌜ T , T-set ⌝ x _ = (T [ !◇ (𝕪 x) ]) ,s T-set
  Tm.naturality ⌜ T , T-set ⌝ {x = x} {y = y} f _ = ty-subst-seq-cong (!◇ (𝕪 y) ∷ to-𝕪⇒* f ◼) (!◇ (𝕪 x) ◼) T (◇-terminal (𝕪 x) _ _)

  El : Tm ◇ (𝒰 ℓ r) → Ty {C = C} ◇ ℓ r
  type (El 𝑇) x _ = type (h-set-type (𝑇 ⟨ x , tt ⟩')) x hom-id
  morph (El 𝑇) f _ t = func (from (Tm.naturality 𝑇 f ≡-refl)) (h-set-type (𝑇 ⟨ _ , tt ⟩') ⟪ f , ≡-trans hom-idˡ (≡-sym hom-idʳ) ⟫ t)
  morph-cong (El 𝑇) {y = y} f _ = func-cong (from (Tm.naturality 𝑇 f ≡-refl)) ∘ morph-cong (h-set-type (𝑇 ⟨ y , tt ⟩')) f (≡-trans hom-idˡ (≡-sym hom-idʳ))
  morph-hom-cong (El 𝑇) ≡-refl = ty≈-refl (h-set-type (𝑇 ⟨ _ , _ ⟩'))
  morph-id (El 𝑇) t = {!!}
    -- This does not work, the problem with elimination persists, namely that
    -- we cannot know that the isomorphism arising from naturality of 𝑇 is
    -- functorial (i.e. produces the identity isomorphism for hom-id and
    -- respects composition). A possible solution would be to define semantic
    -- types as 2-setoid-valued presheaves and let elimination make the
    -- "2-cells" trivial (i.e. allow elimination to h-sets, similar to how the
    -- curent universe from the alternative above allows you to eliminate to h-props).
  morph-comp (El 𝑇) = {!!}
