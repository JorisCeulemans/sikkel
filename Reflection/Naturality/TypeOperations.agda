--------------------------------------------------
-- Definition of nullary, unary and binary type operations.
--------------------------------------------------

module Reflection.Naturality.TypeOperations where

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.ClosedTypes

private
  variable
    C D D' : Category


--------------------------------------------------
-- Definition of endofunctors on a context category.

CtxOp : Category → Category → Set₁
CtxOp C D = Ctx C → Ctx D

record IsCtxFunctor (Φ : CtxOp C D) : Set₁ where
  field
    ctx-map : {Δ : Ctx C} {Γ : Ctx C} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-id : {Γ : Ctx C} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : {Δ : Ctx C} {Γ : Ctx C}  {Θ : Ctx C} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 ctx-map (τ ⊚ σ) ≅ˢ ctx-map τ ⊚ ctx-map σ

open IsCtxFunctor {{...}} public

instance
  id-ctx-functor : IsCtxFunctor {C = C} (λ Γ → Γ)
  ctx-map {{id-ctx-functor}} σ = σ
  ctx-map-id {{id-ctx-functor}} = ≅ˢ-refl
  ctx-map-⊚ {{id-ctx-functor}} _ _ = ≅ˢ-refl


--------------------------------------------------
-- Definition of (natural) nullary, unary and binary type operations.

NullaryTypeOp : Category → Set₁
NullaryTypeOp = ClosedType

IsNullaryNatural : NullaryTypeOp C → Set₁
IsNullaryNatural = IsClosedNatural

open CwF-Structure.ClosedTypes public renaming (closed-natural to natural-nul)

UnaryTypeOp : CtxOp C D → Set₁
UnaryTypeOp {C = C} Φ = {Γ : Ctx C} → Ty (Φ Γ) → Ty Γ

record IsUnaryNatural {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} (F : UnaryTypeOp Φ) : Set₁ where
  field
    natural-un : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) {T : Ty (Φ Γ)} →
                 (F T) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ])
    cong-un : {Γ : Ctx C} {T : Ty (Φ Γ)} {T' : Ty (Φ Γ)} →
              T ≅ᵗʸ T' → F T ≅ᵗʸ F T'

open IsUnaryNatural {{...}} public

BinaryTypeOp : CtxOp C D → CtxOp C D' → Set₁
BinaryTypeOp {C = C} Φ Ψ = {Γ : Ctx C} → Ty (Φ Γ) → Ty (Ψ Γ) → Ty Γ

record IsBinaryNatural
  {Φ : CtxOp C D} {Ψ : CtxOp C D'}
  {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}}
  (F : BinaryTypeOp Φ Ψ) : Set₁ where

  field
    natural-bin : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) →
                  {T : Ty (Φ Γ)} {S : Ty (Ψ Γ)} →
                  (F T S) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ]) (S [ ctx-map σ ])
    cong-bin : {Γ : Ctx C}
               {T : Ty (Φ Γ)} {T' : Ty (Φ Γ)} {S : Ty (Ψ Γ)} {S' : Ty (Ψ Γ)} →
               T ≅ᵗʸ T' → S ≅ᵗʸ S' → F T S ≅ᵗʸ F T' S'

open IsBinaryNatural {{...}} public
