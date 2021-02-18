--------------------------------------------------
-- Definition of nullary, unary and binary type operations.
--------------------------------------------------

module Reflection.Naturality.TypeOperations where

open import Level

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.ClosedTypes

private
  variable
    f : Level → Level
    C D D' : Category


--------------------------------------------------
-- Definition of endofunctors on a context category.

CtxOp : Category → Category → Setω
CtxOp C D = ∀ {ℓ} → Ctx C ℓ → Ctx D ℓ

record IsCtxFunctor (Φ : CtxOp C D) : Setω where
  field
    ctx-map : ∀ {ℓ ℓ'} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-id : ∀ {ℓ} {Γ : Ctx C ℓ} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'}  {Θ : Ctx C ℓ''} →
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

NullaryTypeOp : Category → (Level → Level) → Setω
NullaryTypeOp = ClosedType

IsNullaryNatural : NullaryTypeOp C f → Setω
IsNullaryNatural = IsClosedNatural

open CwF-Structure.ClosedTypes public renaming (closed-natural to natural-nul)

UnaryTypeOp : CtxOp C D → (Level → Level → Level) → Setω
UnaryTypeOp {C = C} Φ f = ∀ {ℓc ℓt} {Γ : Ctx C ℓc} → Ty (Φ Γ) ℓt → Ty Γ (f ℓc ℓt)

record IsUnaryNatural {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} {f} (F : UnaryTypeOp Φ f) : Setω where
  field
    natural-un : ∀ {ℓc ℓc' ℓt} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) {T : Ty (Φ Γ) ℓt} →
                 (F T) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ])
    cong-un : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc}
              {T : Ty (Φ Γ) ℓt} {T' : Ty (Φ Γ) ℓt'} →
              T ≅ᵗʸ T' → F T ≅ᵗʸ F T'

open IsUnaryNatural {{...}} public

BinaryTypeOp : CtxOp C D → CtxOp C D' → (Level → Level → Level → Level) → Setω
BinaryTypeOp {C = C} Φ Ψ f = ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc} → Ty (Φ Γ) ℓt → Ty (Ψ Γ) ℓt' → Ty Γ (f ℓc ℓt ℓt')

record IsBinaryNatural
  {Φ : CtxOp C D} {Ψ : CtxOp C D'}
  {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}}
  {f} (F : BinaryTypeOp Φ Ψ f) : Setω where

  field
    natural-bin : ∀ {ℓc ℓc' ℓt ℓt'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                  {T : Ty (Φ Γ) ℓt} {S : Ty (Ψ Γ) ℓt'} →
                  (F T S) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ]) (S [ ctx-map σ ])
    cong-bin : ∀ {ℓc ℓt ℓt' ℓs ℓs'} {Γ : Ctx C ℓc}
               {T : Ty (Φ Γ) ℓt} {T' : Ty (Φ Γ) ℓt'} {S : Ty (Ψ Γ) ℓs} {S' : Ty (Ψ Γ) ℓs'} →
               T ≅ᵗʸ T' → S ≅ᵗʸ S' → F T S ≅ᵗʸ F T' S'

open IsBinaryNatural {{...}} public
