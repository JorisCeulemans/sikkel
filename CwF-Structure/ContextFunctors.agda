--------------------------------------------------
-- Definition of functors on a context category
--------------------------------------------------

module CwF-Structure.ContextFunctors where

open import Level

open import Categories
open import CwF-Structure.Contexts


CtxOp : Category → Category → Setω
CtxOp C D = ∀ {ℓ} → Ctx C ℓ → Ctx D ℓ

record IsCtxFunctor {C}{D} (Φ : CtxOp C D) : Setω where
  field
    ctx-map : ∀ {ℓ ℓ'} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-id : ∀ {ℓ} {Γ : Ctx C ℓ} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'}  {Θ : Ctx C ℓ''} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 ctx-map (τ ⊚ σ) ≅ˢ ctx-map τ ⊚ ctx-map σ

open IsCtxFunctor {{...}} public

instance
  id-ctx-functor : ∀ {C} → IsCtxFunctor {C = C} (λ Γ → Γ)
  ctx-map {{id-ctx-functor}} σ = σ
  ctx-map-id {{id-ctx-functor}} = ≅ˢ-refl
  ctx-map-⊚ {{id-ctx-functor}} _ _ = ≅ˢ-refl
