--------------------------------------------------
-- Functors on context categories and natural transformations between them
--------------------------------------------------

module Model.CwF-Structure.ContextFunctor where

open import Data.Product renaming (_,_ to [_,_])
open import Function
import Function.Construct.Composition as Composition
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Reasoning.Syntax
open import Preliminaries

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextEquivalence
open import Model.CwF-Structure.Type

private
  variable
    C D : BaseCategory

infix 1 _≅ᶜᵗ_ _≅ᶜᶠ_
infixl 20 _ⓝ-vert_


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

private variable
  Φ Ψ Ω : CtxFunctor C D

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


record _≅ᶜᵗ_ {Φ Ψ : CtxFunctor C D} (α β : CtxNatTransf Φ Ψ) : Set₁ where
  field
    transf-op-eq : ∀ {Γ} → transf-op α Γ ≅ˢ transf-op β Γ
open _≅ᶜᵗ_ public

module _ {Φ Ψ : CtxFunctor C D} where
  reflᶜᵗ : {α : CtxNatTransf Φ Ψ} → α ≅ᶜᵗ α
  transf-op-eq reflᶜᵗ = reflˢ

  symᶜᵗ : {α β : CtxNatTransf Φ Ψ} → α ≅ᶜᵗ β → β ≅ᶜᵗ α
  transf-op-eq (symᶜᵗ 𝓮) = symˢ (transf-op-eq 𝓮)

  transᶜᵗ : {α1 α2 α3 : CtxNatTransf Φ Ψ} → α1 ≅ᶜᵗ α2 → α2 ≅ᶜᵗ α3 → α1 ≅ᶜᵗ α3
  transf-op-eq (transᶜᵗ 𝓮 𝓮') = transˢ (transf-op-eq 𝓮) (transf-op-eq 𝓮')

module ≅ᶜᵗ-Reasoning {C D} {Φ Ψ : CtxFunctor C D} where
  open begin-syntax {A = CtxNatTransf Φ Ψ} _≅ᶜᵗ_ id public
  open ≅-syntax {A = CtxNatTransf Φ Ψ} _≅ᶜᵗ_ _≅ᶜᵗ_ transᶜᵗ symᶜᵗ public
  open end-syntax {A = CtxNatTransf Φ Ψ} _≅ᶜᵗ_ reflᶜᵗ public


ctx-transf-setoid : (Φ Ψ : CtxFunctor C D) → Setoid _ _
Setoid.Carrier (ctx-transf-setoid Φ Ψ) = CtxNatTransf Φ Ψ
Setoid._≈_ (ctx-transf-setoid Φ Ψ) = _≅ᶜᵗ_
IsEquivalence.refl (Setoid.isEquivalence (ctx-transf-setoid Φ Ψ)) = reflᶜᵗ
IsEquivalence.sym (Setoid.isEquivalence (ctx-transf-setoid Φ Ψ)) = symᶜᵗ
IsEquivalence.trans (Setoid.isEquivalence (ctx-transf-setoid Φ Ψ)) = transᶜᵗ


ⓝ-vert-unitʳ : {α : CtxNatTransf Φ Ψ} → α ⓝ-vert id-ctx-transf Φ ≅ᶜᵗ α
transf-op-eq ⓝ-vert-unitʳ = id-subst-unitʳ _

ⓝ-vert-unitˡ : {α : CtxNatTransf Φ Ψ} → id-ctx-transf Ψ ⓝ-vert α ≅ᶜᵗ α
transf-op-eq ⓝ-vert-unitˡ = id-subst-unitˡ _

ⓝ-vert-assoc : {Φ1 Φ2 Φ3 Φ4 : CtxFunctor C D}
               {α34 : CtxNatTransf Φ3 Φ4} {α23 : CtxNatTransf Φ2 Φ3} {α12 : CtxNatTransf Φ1 Φ2} →
               (α34 ⓝ-vert α23) ⓝ-vert α12 ≅ᶜᵗ α34 ⓝ-vert (α23 ⓝ-vert α12)
transf-op-eq ⓝ-vert-assoc = ⊚-assoc

ⓝ-vert-congʳ : {β : CtxNatTransf Ψ Ω} {α α' : CtxNatTransf Φ Ψ} →
               α ≅ᶜᵗ α' → β ⓝ-vert α ≅ᶜᵗ β ⓝ-vert α'
transf-op-eq (ⓝ-vert-congʳ eα) = ⊚-congʳ (transf-op-eq eα)

ⓝ-vert-congˡ : {β β' : CtxNatTransf Ψ Ω} {α : CtxNatTransf Φ Ψ} →
               β ≅ᶜᵗ β' → β ⓝ-vert α ≅ᶜᵗ β' ⓝ-vert α
transf-op-eq (ⓝ-vert-congˡ eα) = ⊚-congˡ (transf-op-eq eα)


--------------------------------------------------
-- Natural isomorphisms between context functors

record _≅ᶜᶠ_ (Φ Ψ : CtxFunctor C D) : Set₁ where
  no-eta-equality

  field
    from : CtxNatTransf Φ Ψ
    to : CtxNatTransf Ψ Φ
    isoˡ : to ⓝ-vert from ≅ᶜᵗ id-ctx-transf Φ
    isoʳ : from ⓝ-vert to ≅ᶜᵗ id-ctx-transf Ψ
open _≅ᶜᶠ_ public

reflᶜᶠ : Φ ≅ᶜᶠ Φ
from (reflᶜᶠ {Φ = Φ}) = id-ctx-transf Φ
to (reflᶜᶠ {Φ = Φ}) = id-ctx-transf Φ
isoˡ reflᶜᶠ = ⓝ-vert-unitˡ
isoʳ reflᶜᶠ = ⓝ-vert-unitˡ

symᶜᶠ : Ψ ≅ᶜᶠ Φ → Φ ≅ᶜᶠ Ψ
from (symᶜᶠ Ψ=Φ) = to Ψ=Φ
to (symᶜᶠ Ψ=Φ) = from Ψ=Φ
isoˡ (symᶜᶠ Ψ=Φ) = isoʳ Ψ=Φ
isoʳ (symᶜᶠ Ψ=Φ) = isoˡ Ψ=Φ

transᶜᶠ : Ψ ≅ᶜᶠ Φ → Φ ≅ᶜᶠ Ω → Ψ ≅ᶜᶠ Ω
from (transᶜᶠ Ψ=Φ Φ=Ω) = from Φ=Ω ⓝ-vert from Ψ=Φ
to (transᶜᶠ Ψ=Φ Φ=Ω) = to Ψ=Φ ⓝ-vert to Φ=Ω
isoˡ (transᶜᶠ Ψ=Φ Φ=Ω) =
  begin
    (to Ψ=Φ ⓝ-vert to Φ=Ω) ⓝ-vert (from Φ=Ω ⓝ-vert from Ψ=Φ)
  ≅⟨ ⓝ-vert-assoc ⟩
    to Ψ=Φ ⓝ-vert (to Φ=Ω ⓝ-vert (from Φ=Ω ⓝ-vert from Ψ=Φ))
  ≅⟨ ⓝ-vert-congʳ ⓝ-vert-assoc ⟨
    to Ψ=Φ ⓝ-vert ((to Φ=Ω ⓝ-vert from Φ=Ω) ⓝ-vert from Ψ=Φ)
  ≅⟨ ⓝ-vert-congʳ (ⓝ-vert-congˡ (isoˡ Φ=Ω)) ⟩
    to Ψ=Φ ⓝ-vert (id-ctx-transf _ ⓝ-vert from Ψ=Φ)
  ≅⟨ ⓝ-vert-congʳ ⓝ-vert-unitˡ ⟩
    to Ψ=Φ ⓝ-vert from Ψ=Φ
  ≅⟨ isoˡ Ψ=Φ ⟩
    id-ctx-transf _ ∎
  where open ≅ᶜᵗ-Reasoning
isoʳ (transᶜᶠ Ψ=Φ Φ=Ω) =
  begin
    (from Φ=Ω ⓝ-vert from Ψ=Φ) ⓝ-vert (to Ψ=Φ ⓝ-vert to Φ=Ω)
  ≅⟨ ⓝ-vert-assoc ⟩
    from Φ=Ω ⓝ-vert (from Ψ=Φ ⓝ-vert (to Ψ=Φ ⓝ-vert to Φ=Ω))
  ≅⟨ ⓝ-vert-congʳ ⓝ-vert-assoc ⟨
    from Φ=Ω ⓝ-vert ((from Ψ=Φ ⓝ-vert to Ψ=Φ) ⓝ-vert to Φ=Ω)
  ≅⟨ ⓝ-vert-congʳ (ⓝ-vert-congˡ (isoʳ Ψ=Φ)) ⟩
    from Φ=Ω ⓝ-vert (id-ctx-transf _ ⓝ-vert to Φ=Ω)
  ≅⟨ ⓝ-vert-congʳ ⓝ-vert-unitˡ ⟩
    from Φ=Ω ⓝ-vert to Φ=Ω
  ≅⟨ isoʳ Φ=Ω ⟩
    id-ctx-transf _ ∎
  where open ≅ᶜᵗ-Reasoning


-- From a natural isomorphism between context functors, we can
-- construct Agda isomorphisms for the types of natural
-- transformations to and from these functors.

ctx-functor-iso-transf-isoʳ : {Φ Ψ Ψ' : CtxFunctor C D} → Ψ ≅ᶜᶠ Ψ' →
                              Inverse (ctx-transf-setoid Φ Ψ) (ctx-transf-setoid Φ Ψ')
Inverse.to (ctx-functor-iso-transf-isoʳ Ψ~Ψ') α = from Ψ~Ψ' ⓝ-vert α
Inverse.from (ctx-functor-iso-transf-isoʳ Ψ~Ψ') α = to Ψ~Ψ' ⓝ-vert α
Inverse.to-cong (ctx-functor-iso-transf-isoʳ Ψ~Ψ') = ⓝ-vert-congʳ
Inverse.from-cong (ctx-functor-iso-transf-isoʳ Ψ~Ψ') = ⓝ-vert-congʳ
Inverse.inverse (ctx-functor-iso-transf-isoʳ Ψ~Ψ') =
  [ (λ eα → transᶜᵗ (ⓝ-vert-congʳ eα) (transᶜᵗ (symᶜᵗ ⓝ-vert-assoc) (transᶜᵗ (ⓝ-vert-congˡ (isoʳ Ψ~Ψ')) ⓝ-vert-unitˡ)))
  , (λ eα → transᶜᵗ (ⓝ-vert-congʳ eα) (transᶜᵗ (symᶜᵗ ⓝ-vert-assoc) (transᶜᵗ (ⓝ-vert-congˡ (isoˡ Ψ~Ψ')) ⓝ-vert-unitˡ)))
  ]

ctx-functor-iso-transf-isoˡ : {Φ Φ' Ψ : CtxFunctor C D} → Φ ≅ᶜᶠ Φ' →
                              Inverse (ctx-transf-setoid Φ Ψ) (ctx-transf-setoid Φ' Ψ)
Inverse.to (ctx-functor-iso-transf-isoˡ Φ~Φ') α = α ⓝ-vert to Φ~Φ'
Inverse.from (ctx-functor-iso-transf-isoˡ Φ~Φ') α = α ⓝ-vert from Φ~Φ'
Inverse.to-cong (ctx-functor-iso-transf-isoˡ Φ~Φ') = ⓝ-vert-congˡ
Inverse.from-cong (ctx-functor-iso-transf-isoˡ Φ~Φ') = ⓝ-vert-congˡ
Inverse.inverse (ctx-functor-iso-transf-isoˡ Φ~Φ') =
  [ (λ eα → transᶜᵗ (ⓝ-vert-congˡ eα) (transᶜᵗ ⓝ-vert-assoc (transᶜᵗ (ⓝ-vert-congʳ (isoʳ Φ~Φ')) ⓝ-vert-unitʳ)))
  , (λ eα → transᶜᵗ (ⓝ-vert-congˡ eα) (transᶜᵗ ⓝ-vert-assoc (transᶜᵗ (ⓝ-vert-congʳ (isoˡ Φ~Φ')) ⓝ-vert-unitʳ)))
  ]

ctx-functor-iso-transf-iso : {Φ Φ' Ψ Ψ' : CtxFunctor C D} →
                             Φ ≅ᶜᶠ Φ' → Ψ ≅ᶜᶠ Ψ' →
                             Inverse (ctx-transf-setoid Φ Ψ) (ctx-transf-setoid Φ' Ψ')
ctx-functor-iso-transf-iso Φ~Φ' Ψ~Ψ' =
  Composition.inverse (ctx-functor-iso-transf-isoˡ Φ~Φ') (ctx-functor-iso-transf-isoʳ Ψ~Ψ')
