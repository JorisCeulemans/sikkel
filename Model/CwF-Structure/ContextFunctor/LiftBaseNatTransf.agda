module Model.CwF-Structure.ContextFunctor.LiftBaseNatTransf where

open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Function.Consequences.Setoid
import Function.Construct.Composition as Composition
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (naturality)

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextFunctor
open import Model.CwF-Structure.ContextFunctor.LiftBaseFunctor
open import Model.CwF-Structure.Yoneda

open BaseCategory
open BaseFunctor
open BaseNatTransf

private variable
  C D : BaseCategory


module _
  {C D : BaseCategory}
  {F G : BaseFunctor C D}
  (α : BaseNatTransf F G)
  where

  -- A natural transformation between base functors can be lifted to a
  -- natural transformation between the lifted context functors.
  lift-transf : CtxNatTransf (lift-functor G) (lift-functor F)
  func (transf-op lift-transf Γ) {x = x} γ = Γ ⟪ transf-op α x ⟫ γ
  naturality (transf-op lift-transf Γ) {f = f} = ctx-cong-2-2 Γ (naturality α f)
  eq (naturality lift-transf σ) γ = naturality σ


lift-transf-cong : {C D : BaseCategory} {F G : BaseFunctor C D}
                   {α α' : BaseNatTransf F G} →
                   α ≅ᵇᵗ α' →
                   lift-transf α ≅ᶜᵗ lift-transf α'
eq (transf-op-eq (lift-transf-cong 𝓮) {Γ = Γ}) {x = x} γ =
  cong (λ f → Γ ⟪ f ⟫ γ) (_≅ᵇᵗ_.transf-op-eq 𝓮 x)


-- In the following module, we will show that every natural
-- transformation between lifted context functors is of the form
-- lift-trans α for some natural tranformation α between the base
-- functors.

module _
  {C D : BaseCategory}
  {F G : BaseFunctor C D}
  (β : CtxNatTransf (lift-functor G) (lift-functor F))
  where

  unlift-transf : BaseNatTransf F G
  transf-op unlift-transf x = func (transf-op β (𝕪 (ob G x))) (hom-id D)
  naturality unlift-transf {x = x} {y} f =
    begin
      (func (transf-op β (𝕪 (ob G y))) (hom-id D)) ∙[ D ] hom F f
    ≡⟨ naturality (transf-op β (𝕪 (ob G y))) ⟩
      func (transf-op β (𝕪 (ob G y))) (hom-id D ∙[ D ] hom G f)
    ≡⟨ cong (func (transf-op β (𝕪 (ob G y)))) (trans (hom-idˡ D) (sym (hom-idʳ D))) ⟩
      func (transf-op β (𝕪 (ob G y))) (hom G f ∙[ D ] hom-id D)
    ≡⟨ eq (naturality β (to-𝕪⇒𝕪 (hom G f))) (hom-id D) ⟩
      hom G f ∙[ D ] func (transf-op β (𝕪 (ob G x))) (hom-id D) ∎
    where open ≡-Reasoning

unlift-transf-cong : {C D : BaseCategory} {F G : BaseFunctor C D}
                     {β β' : CtxNatTransf (lift-functor G) (lift-functor F)} →
                     β ≅ᶜᵗ β' → unlift-transf β ≅ᵇᵗ unlift-transf β'
_≅ᵇᵗ_.transf-op-eq (unlift-transf-cong 𝓮) x = eq (transf-op-eq 𝓮) _

module _
  {C D : BaseCategory}
  {F G : BaseFunctor C D}
  where

  lift-unlift-transf : (β : CtxNatTransf (lift-functor G) (lift-functor F)) →
                       lift-transf (unlift-transf β) ≅ᶜᵗ β
  eq (transf-op-eq (lift-unlift-transf β) {Γ = Γ}) {x = x} γ =
    begin
      Γ ⟪ func (transf-op β (𝕪 (ob G x))) (hom-id D) ⟫ γ
    ≡⟨ eq (naturality β (to-𝕪⇒* γ)) (hom-id D) ⟨
      func (transf-op β Γ) (Γ ⟪ hom-id D ⟫ γ)
    ≡⟨ cong (func (transf-op β Γ)) (ctx-id Γ) ⟩
      func (transf-op β Γ) γ ∎
    where open ≡-Reasoning

  unlift-lift-transf : (α : BaseNatTransf F G) →
                       unlift-transf (lift-transf α) ≅ᵇᵗ α
  _≅ᵇᵗ_.transf-op-eq (unlift-lift-transf α) x = hom-idˡ D

base-transf-setoid : (F G : BaseFunctor C D) → Setoid _ _
Setoid.Carrier (base-transf-setoid F G) = BaseNatTransf F G
Setoid._≈_ (base-transf-setoid F G) = _≅ᵇᵗ_
IsEquivalence.refl (Setoid.isEquivalence (base-transf-setoid F G)) = reflᵇᵗ
IsEquivalence.sym (Setoid.isEquivalence (base-transf-setoid F G)) = symᵇᵗ
IsEquivalence.trans (Setoid.isEquivalence (base-transf-setoid F G)) = transᵇᵗ


-- As a conclusion, given 2 base functors F and G, we have an
-- isomorphism between the Agda types of base transformations from F
-- to G and context transformations from lift-functor G to
-- lift-functor F.
lift-transf-iso : (F G : BaseFunctor C D) →
                  Inverse (base-transf-setoid F G) (ctx-transf-setoid (lift-functor G) (lift-functor F))
Inverse.to (lift-transf-iso F G) = lift-transf
Inverse.from (lift-transf-iso F G) = unlift-transf
Inverse.to-cong (lift-transf-iso F G) = lift-transf-cong
Inverse.from-cong (lift-transf-iso F G) = unlift-transf-cong
Inverse.inverse (lift-transf-iso F G) =
  [ strictlyInverseˡ⇒inverseˡ (base-transf-setoid F G) (ctx-transf-setoid _ _) lift-transf-cong lift-unlift-transf
  , strictlyInverseʳ⇒inverseʳ (base-transf-setoid F G) (ctx-transf-setoid _ _) {f = lift-transf} unlift-transf-cong unlift-lift-transf
  ]


lifted-functor-transf-eq : {Φ Ψ : CtxFunctor C D} (ilΦ : IsLiftedFunctor Φ) (ilΨ : IsLiftedFunctor Ψ)
                           {β β' : CtxNatTransf Φ Ψ} →
                           unlift-transf (Inverse.from (ctx-functor-iso-transf-iso (is-lifted ilΦ) (is-lifted ilΨ)) β)
                             ≅ᵇᵗ unlift-transf (Inverse.from (ctx-functor-iso-transf-iso (is-lifted ilΦ) (is-lifted ilΨ)) β')
                           →
                           β ≅ᶜᵗ β'
lifted-functor-transf-eq {Φ = Φ} {Ψ} ilΦ ilΨ =
  let inverse = Composition.inverse (lift-transf-iso (base-functor ilΨ) (base-functor ilΦ))
                                    (ctx-functor-iso-transf-iso (is-lifted ilΦ) (is-lifted ilΨ))
  in
  inverseʳ⇒injective (ctx-transf-setoid Φ Ψ)
                     (base-transf-setoid (base-functor ilΨ) (base-functor ilΦ))
                     (Inverse.from inverse)
                     (Inverse.inverseˡ inverse)
