module Model.CwF-Structure.ContextFunctor.LiftBaseNatTransf where

open import Relation.Binary.PropositionalEquality hiding (naturality)

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextFunctor
open import Model.CwF-Structure.ContextFunctor.LiftBaseFunctor
open import Model.CwF-Structure.Yoneda

open BaseCategory
open BaseFunctor
open BaseNatTransf


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

  lift-unlift-transf : β ≅ᶜᵗ lift-transf unlift-transf 
  eq (transf-op-eq lift-unlift-transf {Γ = Γ}) {x = x} γ =
    begin
      func (transf-op β Γ) γ
    ≡⟨ cong (func (transf-op β Γ)) (ctx-id Γ) ⟨
      func (transf-op β Γ) (Γ ⟪ hom-id D ⟫ γ)
    ≡⟨ eq (naturality β (to-𝕪⇒* γ)) (hom-id D) ⟩
      Γ ⟪ func (transf-op β (𝕪 (ob G x))) (hom-id D) ⟫ γ ∎
    where open ≡-Reasoning

module _
  {C D : BaseCategory}
  {F G : BaseFunctor C D}
  (α : BaseNatTransf F G)
  where

  unlift-lift-transf : α ≅ᵇᵗ unlift-transf (lift-transf α)
  _≅ᵇᵗ_.transf-op-eq unlift-lift-transf x = sym (hom-idˡ D)
