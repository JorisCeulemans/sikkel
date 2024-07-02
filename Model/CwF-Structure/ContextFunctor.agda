--------------------------------------------------
-- Functors on context categories and natural transformations between them
--------------------------------------------------

module Model.CwF-Structure.ContextFunctor where

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextEquivalence
open import Model.CwF-Structure.Type

private
  variable
    C D : BaseCategory


--------------------------------------------------
-- Definition of functors between context categories

CtxOp : BaseCategory → BaseCategory → Set₁
CtxOp C D = Ctx C → Ctx D

record IsCtxFunctor (Φ : CtxOp C D) : Set₁ where
  no-eta-equality
  field
    ctx-map : {Δ Γ : Ctx C} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-cong : {Δ Γ : Ctx C} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ctx-map σ ≅ˢ ctx-map τ
    ctx-map-id : {Γ : Ctx C} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : {Δ Γ Θ : Ctx C} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 ctx-map (τ ⊚ σ) ≅ˢ ctx-map τ ⊚ ctx-map σ

  ctx-map-inverse : {Δ Γ : Ctx C} {σ : Δ ⇒ Γ} {τ : Γ ⇒ Δ} →
                    τ ⊚ σ ≅ˢ id-subst Δ → ctx-map τ ⊚ ctx-map σ ≅ˢ id-subst (Φ Δ)
  ctx-map-inverse {Δ = Δ} {σ = σ} {τ = τ} ε = begin
      ctx-map τ ⊚ ctx-map σ
    ≅⟨ ctx-map-⊚ τ σ ⟨
      ctx-map (τ ⊚ σ)
    ≅⟨ ctx-map-cong ε ⟩
      ctx-map (id-subst Δ)
    ≅⟨ ctx-map-id ⟩
      id-subst (Φ Δ) ∎
    where open ≅ˢ-Reasoning

  ctx-map-cong-2-1 : {Γ Δ Θ : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ : Γ ⇒ Θ} →
                     σ2 ⊚ σ1 ≅ˢ τ → ctx-map σ2 ⊚ ctx-map σ1 ≅ˢ ctx-map τ
  ctx-map-cong-2-1 {σ1 = σ1} {σ2} {τ} ε = transˢ (symˢ (ctx-map-⊚ σ2 σ1)) (ctx-map-cong ε)

  ctx-map-cong-2-2 : {Γ Δ Δ' Θ : Ctx C} {σ1 : Γ ⇒ Δ} {τ1 : Δ ⇒ Θ} {σ2 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ} →
                     τ1 ⊚ σ1 ≅ˢ τ2 ⊚ σ2 → ctx-map τ1 ⊚ ctx-map σ1 ≅ˢ ctx-map τ2 ⊚ ctx-map σ2
  ctx-map-cong-2-2 {σ1 = σ1} {τ1} {σ2} {τ2} ε = begin
      ctx-map τ1 ⊚ ctx-map σ1
    ≅⟨ ctx-map-⊚ τ1 σ1 ⟨
      ctx-map (τ1 ⊚ σ1)
    ≅⟨ ctx-map-cong ε ⟩
      ctx-map (τ2 ⊚ σ2)
    ≅⟨ ctx-map-⊚ τ2 σ2 ⟩
      ctx-map τ2 ⊚ ctx-map σ2 ∎
    where open ≅ˢ-Reasoning

  ty-subst-ctx-map-2-0 : {Γ Δ : Ctx C} {σ : Δ ⇒ Γ} {τ : Γ ⇒ Δ} (T : Ty (Φ Γ)) →
                         σ ⊚ τ ≅ˢ id-subst Γ →
                         T [ ctx-map σ ] [ ctx-map τ ] ≅ᵗʸ T
  ty-subst-ctx-map-2-0 T ε =
    transᵗʸ (ty-subst-comp T _ _) (
    transᵗʸ (ty-subst-cong-subst (ctx-map-inverse ε) T) (
    ty-subst-id T))

open IsCtxFunctor {{...}} public

instance
  id-is-ctx-functor : ∀ {C} → IsCtxFunctor {C = C} (λ Γ → Γ)
  ctx-map {{id-is-ctx-functor}} σ = σ
  ctx-map-cong {{id-is-ctx-functor}} ε = ε
  ctx-map-id {{id-is-ctx-functor}} = reflˢ
  ctx-map-⊚ {{id-is-ctx-functor}} _ _ = reflˢ

-- This operation is not made available for instance resolution because otherwise
--   there would be infinitely many instances of IsCtxFunctor for any context
--   operation (by pre- or postcomposition with the identity operation).
composed-functor : {C1 C2 C3 : BaseCategory} {Φ : CtxOp C2 C3} {Ψ : CtxOp C1 C2} →
                   IsCtxFunctor Φ → IsCtxFunctor Ψ → IsCtxFunctor (λ Γ → Φ (Ψ Γ))
ctx-map {{composed-functor φ ψ}} σ = ctx-map {{φ}} (ctx-map {{ψ}} σ)
ctx-map-cong {{composed-functor φ ψ}} ε = ctx-map-cong {{φ}} (ctx-map-cong {{ψ}} ε)
ctx-map-id {{composed-functor φ ψ}} = transˢ (ctx-map-cong {{φ}} (ctx-map-id {{ψ}})) (ctx-map-id {{φ}})
ctx-map-⊚ {{composed-functor φ ψ}} τ σ = transˢ (ctx-map-cong {{φ}} (ctx-map-⊚ {{ψ}} τ σ)) (ctx-map-⊚ {{φ}} _ _)


record CtxFunctor (C D : BaseCategory) : Set₁ where
  no-eta-equality
  field
    ctx-op : CtxOp C D
    is-functor : IsCtxFunctor ctx-op

  ctx-fmap = ctx-map {{is-functor}}
  ctx-fmap-cong = ctx-map-cong {{is-functor}}
  ctx-fmap-id = ctx-map-id {{is-functor}}
  ctx-fmap-⊚ = ctx-map-⊚ {{is-functor}}
  ctx-fmap-inverse = ctx-map-inverse {{is-functor}}
  ctx-fmap-cong-2-1 = ctx-map-cong-2-1 {{is-functor}}
  ctx-fmap-cong-2-2 = ctx-map-cong-2-2 {{is-functor}}
  ty-subst-ctx-fmap-2-0 = ty-subst-ctx-map-2-0 {{is-functor}}

open CtxFunctor public

id-ctx-functor : CtxFunctor C C
ctx-op id-ctx-functor = λ Γ → Γ
is-functor id-ctx-functor = id-is-ctx-functor

_ⓕ_ : ∀ {C1 C2 C3} → CtxFunctor C2 C3 → CtxFunctor C1 C2 → CtxFunctor C1 C3
ctx-op (Φ ⓕ Ψ) = λ Γ → ctx-op Φ (ctx-op Ψ Γ)
is-functor (Φ ⓕ Ψ) = composed-functor (is-functor Φ) (is-functor Ψ)

ctx-functor-cong : (F : CtxFunctor C D) {Γ Δ : Ctx C} → Γ ≅ᶜ Δ → ctx-op F Γ ≅ᶜ ctx-op F Δ
from (ctx-functor-cong F Γ=Δ) = ctx-fmap F (from Γ=Δ)
to (ctx-functor-cong F Γ=Δ) = ctx-fmap F (to Γ=Δ)
isoˡ (ctx-functor-cong F Γ=Δ) = ctx-fmap-inverse F (isoˡ Γ=Δ)
isoʳ (ctx-functor-cong F Γ=Δ) = ctx-fmap-inverse F (isoʳ Γ=Δ)


--------------------------------------------------
-- Natural transformations between context functors

record CtxNatTransf (Φ Ψ : CtxFunctor C D) : Set₁ where
  no-eta-equality
  field
    transf-op : (Γ : Ctx C) → ctx-op Φ Γ ⇒ ctx-op Ψ Γ
    naturality : ∀ {Δ Γ} (σ : Δ ⇒ Γ) → transf-op Γ ⊚ ctx-fmap Φ σ ≅ˢ ctx-fmap Ψ σ ⊚ transf-op Δ

open CtxNatTransf public

id-ctx-transf : (Φ : CtxFunctor C D) → CtxNatTransf Φ Φ
transf-op (id-ctx-transf Φ) Γ = id-subst (ctx-op Φ Γ)
naturality (id-ctx-transf Φ) σ = transˢ (id-subst-unitˡ (ctx-fmap Φ σ))
                                        (symˢ (id-subst-unitʳ (ctx-fmap Φ σ)))

-- Vertical composition of natural transformations
_ⓝ-vert_ : {Φ Ψ Ω : CtxFunctor C D} → CtxNatTransf Ψ Ω → CtxNatTransf Φ Ψ → CtxNatTransf Φ Ω
transf-op (η ⓝ-vert ζ) Γ = transf-op η Γ ⊚ transf-op ζ Γ
naturality (_ⓝ-vert_ {Φ = Φ} {Ψ} {Ω} η ζ) {Δ = Δ} {Γ} σ = begin
    (transf-op η Γ ⊚ transf-op ζ Γ) ⊚ ctx-fmap Φ σ
  ≅⟨ ⊚-assoc ⟩
    transf-op η Γ ⊚ (transf-op ζ Γ ⊚ ctx-fmap Φ σ)
  ≅⟨ ⊚-congʳ (naturality ζ σ) ⟩
    transf-op η Γ ⊚ (ctx-fmap Ψ σ ⊚ transf-op ζ Δ)
  ≅⟨ ⊚-assoc ⟨
    (transf-op η Γ ⊚ ctx-fmap Ψ σ) ⊚ transf-op ζ Δ
  ≅⟨ ⊚-congˡ (naturality η σ) ⟩
    (ctx-fmap Ω σ ⊚ transf-op η Δ) ⊚ transf-op ζ Δ
  ≅⟨ ⊚-assoc ⟩
    ctx-fmap Ω σ ⊚ (transf-op η Δ ⊚ transf-op ζ Δ) ∎
  where open ≅ˢ-Reasoning

-- Horizontal composition of natural transformations
_ⓝ-hor_ : {C1 C2 C3 : BaseCategory} {Φ Φ' : CtxFunctor C2 C3} {Ψ Ψ' : CtxFunctor C1 C2} →
          CtxNatTransf Φ Φ' → CtxNatTransf Ψ Ψ' → CtxNatTransf (Φ ⓕ Ψ) (Φ' ⓕ Ψ')
transf-op (_ⓝ-hor_ {Φ = Φ} {Φ'} {Ψ} {Ψ'} η ζ) Γ = transf-op η (ctx-op Ψ' Γ) ⊚ ctx-fmap Φ (transf-op ζ Γ)
naturality (_ⓝ-hor_ {Φ = Φ} {Φ'} {Ψ} {Ψ'} η ζ) {Δ = Δ} {Γ} σ = begin
    (transf-op η (ctx-op Ψ' Γ) ⊚ ctx-fmap Φ (transf-op ζ Γ)) ⊚ ctx-fmap Φ (ctx-fmap Ψ σ)
  ≅⟨ ⊚-assoc ⟩
    transf-op η (ctx-op Ψ' Γ) ⊚ (ctx-fmap Φ (transf-op ζ Γ) ⊚ ctx-fmap Φ (ctx-fmap Ψ σ))
  ≅⟨ ⊚-congʳ (ctx-fmap-⊚ Φ _ _) ⟨
    transf-op η (ctx-op Ψ' Γ) ⊚ ctx-fmap Φ (transf-op ζ Γ ⊚ ctx-fmap Ψ σ)
  ≅⟨ ⊚-congʳ (ctx-fmap-cong Φ (naturality ζ σ)) ⟩
    transf-op η (ctx-op Ψ' Γ) ⊚ ctx-fmap Φ (ctx-fmap Ψ' σ ⊚ transf-op ζ Δ)
  ≅⟨ ⊚-congʳ (ctx-fmap-⊚ Φ _ _) ⟩
    transf-op η (ctx-op Ψ' Γ) ⊚ (ctx-fmap Φ (ctx-fmap Ψ' σ) ⊚ ctx-fmap Φ (transf-op ζ Δ))
  ≅⟨ ⊚-assoc ⟨
    (transf-op η (ctx-op Ψ' Γ) ⊚ ctx-fmap Φ (ctx-fmap Ψ' σ)) ⊚ ctx-fmap Φ (transf-op ζ Δ)
  ≅⟨ ⊚-congˡ (naturality η (ctx-fmap Ψ' σ)) ⟩
    (ctx-fmap Φ' (ctx-fmap Ψ' σ) ⊚ (transf-op η (ctx-op Ψ' Δ)) ⊚ ctx-fmap Φ (transf-op ζ Δ))
  ≅⟨ ⊚-assoc ⟩
    ctx-fmap Φ' (ctx-fmap Ψ' σ) ⊚ ((transf-op η (ctx-op Ψ' Δ) ⊚ ctx-fmap Φ (transf-op ζ Δ))) ∎
  where open ≅ˢ-Reasoning
