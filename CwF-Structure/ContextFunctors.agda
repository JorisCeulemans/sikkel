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
    ctx-map : {Δ Γ : Ctx C} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-cong : {Δ Γ : Ctx C} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ctx-map σ ≅ˢ ctx-map τ
    ctx-map-id : {Γ : Ctx C} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : {Δ Γ Θ : Ctx C} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 ctx-map (τ ⊚ σ) ≅ˢ ctx-map τ ⊚ ctx-map σ

open IsCtxFunctor {{...}} public

instance
  id-ctx-functor : ∀ {C} → IsCtxFunctor {C = C} (λ Γ → Γ)
  ctx-map {{id-ctx-functor}} σ = σ
  ctx-map-cong {{id-ctx-functor}} e = e
  ctx-map-id {{id-ctx-functor}} = ≅ˢ-refl
  ctx-map-⊚ {{id-ctx-functor}} _ _ = ≅ˢ-refl

-- This operation is not made available for instance resolution because otherwise
--   there would be infinitely many instances of IsCtxFunctor for any context
--   operation (by pre- or postcomposition with the identity operation).
_ⓕ_ : {C1 C2 C3 : Category} {Φ : CtxOp C2 C3} {Ψ : CtxOp C1 C2} →
      IsCtxFunctor Φ → IsCtxFunctor Ψ → IsCtxFunctor (λ Γ → Φ (Ψ Γ))
ctx-map {{φ ⓕ ψ}} σ = ctx-map {{φ}} (ctx-map {{ψ}} σ)
ctx-map-cong {{φ ⓕ ψ}} e = ctx-map-cong {{φ}} (ctx-map-cong {{ψ}} e)
ctx-map-id {{φ ⓕ ψ}} = ≅ˢ-trans (ctx-map-cong {{φ}} (ctx-map-id {{ψ}})) (ctx-map-id {{φ}})
ctx-map-⊚ {{φ ⓕ ψ}} τ σ = ≅ˢ-trans (ctx-map-cong {{φ}} (ctx-map-⊚ {{ψ}} τ σ)) (ctx-map-⊚ {{φ}} _ _)
