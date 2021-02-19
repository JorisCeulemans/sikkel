--------------------------------------------------
-- Definition of functors on a context category
--------------------------------------------------

module CwF-Structure.ContextFunctors where

open import Level

open import Categories
open import CwF-Structure.Contexts


CtxOp : Category → Category → Set₁
CtxOp C D = Ctx C → Ctx D

record IsCtxFunctor {C}{D} (Φ : CtxOp C D) : Set₁ where
  field
    ctx-map : {Δ : Ctx C} {Γ : Ctx C} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-id : {Γ : Ctx C} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : {Δ : Ctx C} {Γ : Ctx C}  {Θ : Ctx C} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 ctx-map (τ ⊚ σ) ≅ˢ ctx-map τ ⊚ ctx-map σ

open IsCtxFunctor {{...}} public

instance
  id-ctx-functor : ∀ {C} → IsCtxFunctor {C = C} (λ Γ → Γ)
  ctx-map {{id-ctx-functor}} σ = σ
  ctx-map-id {{id-ctx-functor}} = ≅ˢ-refl
  ctx-map-⊚ {{id-ctx-functor}} _ _ = ≅ˢ-refl
