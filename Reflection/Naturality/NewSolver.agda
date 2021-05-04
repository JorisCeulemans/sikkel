module Reflection.Naturality.NewSolver where

open import Relation.Binary.PropositionalEquality using (_≡_; refl) renaming (subst to transp)

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.ContextFunctors
open import Reflection.Naturality.TypeOperations


private
  variable
    C D D' : Category

data Expr (C : Category) : Set₁ where
  con : {Γ : Ctx C} (T : Ty Γ) → Expr C
  nul : (U : NullaryTypeOp C) → {{IsNullaryNatural U}} → Expr C
  un  : {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} →
        (F : UnaryTypeOp Φ) → {{IsUnaryNatural F}} → (e : Expr D) → Expr C
  bin : {Φ : CtxOp C D} {Ψ : CtxOp C D'} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} →
        (F : BinaryTypeOp Φ Ψ) → {{IsBinaryNatural F}} → (e1 : Expr D) (e2 : Expr D') → Expr C
  sub : (e : Expr C) {Δ Γ : Ctx C} (σ : Δ ⇒ Γ) → Expr C

record _And_ {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor _and_
  field
    proj₁ : A
    proj₂ : B
open _And_ public

record _AndAlso_ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  constructor _and-also_
  field
    proj₁ : A
    proj₂ : B proj₁
open _AndAlso_ public

record ⊤ : Set₁ where
  instance constructor tt

instance
  and-instance : ∀ {ℓ} {A B : Set ℓ} → {{A}} → {{B}} → A And B
  and-instance {{a}} {{b}} = a and b

IsValidCtx : Ctx C → Expr C → Set₁
IsValidCtx Γ (con {Δ} T) = Γ ≡ Δ
IsValidCtx Γ (nul U) = ⊤
IsValidCtx Γ (un {Φ = Φ} F e) = IsValidCtx (Φ Γ) e
IsValidCtx Γ (bin {Φ = Φ} {Ψ = Ψ} F e1 e2) = (IsValidCtx (Φ Γ) e1) And (IsValidCtx (Ψ Γ) e2)
IsValidCtx Γ (sub e {Δ} {Θ} σ) = (Γ ≡ Δ) And (IsValidCtx Θ e)

interp-expr : (e : Expr C) (Γ : Ctx C) → {{IsValidCtx Γ e}} → Ty Γ
interp-expr (con T) Γ ⦃ refl ⦄ = T
interp-expr (nul U) Γ ⦃ v ⦄ = U
interp-expr (un {Φ = Φ} F e) Γ ⦃ v ⦄ = F (interp-expr e (Φ Γ))
interp-expr (bin {Φ = Φ} {Ψ = Ψ} F e1 e2) Γ ⦃ v1 and v2 ⦄ = F (interp-expr e1 (Φ Γ) {{v1}}) (interp-expr e2 (Ψ Γ) {{v2}})
interp-expr (sub e σ) Γ ⦃ refl and v ⦄ = interp-expr e _ {{v}} [ σ ]

{-# TERMINATING #-}
Reducible : Expr C → Set₁
Reducible (con T) = ⊤
Reducible (nul U) = ⊤
Reducible (un F e) = Reducible e
Reducible (bin F e1 e2) = Reducible e1 And Reducible e2
Reducible (sub (con T) σ) = ⊤
Reducible (sub (nul U) σ) = ⊤
Reducible (sub (un F e) σ) = Reducible (sub e (ctx-map σ))
Reducible (sub (bin F e1 e2) σ) = Reducible (sub e1 (ctx-map σ)) And Reducible (sub e2 (ctx-map σ))
Reducible (sub (sub e {Δτ} {Γτ} τ) {Δσ} {Γσ} σ) = (Γσ ≡ Δτ) AndAlso λ { refl → Reducible (sub e (τ ⊚ σ)) }

{-# TERMINATING #-}
reduce : (e : Expr C) → {{Reducible e}} → Expr C
reduce (con T) = con T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) {{ r1 and r2 }} = bin F (reduce e1 {{r1}}) (reduce e2 {{r2}})
reduce (sub (con T) σ) = sub (con T) σ
reduce (sub (nul U) σ) = nul U
reduce (sub (un F e) σ) = un F (reduce (sub e (ctx-map σ)))
reduce (sub (bin F e1 e2) σ) {{ r1 and r2 }} = bin F (reduce (sub e1 (ctx-map σ)) {{r1}}) (reduce (sub e2 (ctx-map σ)) {{r2}})
reduce (sub (sub e τ) σ) ⦃ refl and-also r ⦄ = reduce (sub e (τ ⊚ σ)) ⦃ r ⦄

{-# TERMINATING #-}
reduce-valid : (e : Expr C) (Γ : Ctx C) → {{_ : Reducible e}} →
               IsValidCtx Γ e → IsValidCtx Γ (reduce e)
reduce-valid (con T) Γ ⦃ r ⦄ v = v
reduce-valid (nul U) Γ ⦃ r ⦄ v = tt
reduce-valid (un {Φ = Φ} F e) Γ ⦃ r ⦄ v = reduce-valid e (Φ Γ) v
reduce-valid (bin F e1 e2) Γ ⦃ r1 and r2 ⦄ (v1 and v2) = reduce-valid e1 _ {{r1}} v1 and reduce-valid e2 _ {{r2}} v2
reduce-valid (sub (con T) σ) Γ ⦃ r ⦄ v = v
reduce-valid (sub (nul U) σ) Γ ⦃ r ⦄ v = tt
reduce-valid (sub (un F e) σ) Γ ⦃ r ⦄ (refl and v) = reduce-valid (sub e (ctx-map σ)) _ (refl and v)
reduce-valid (sub (bin F e1 e2) σ) Γ ⦃ r1 and r2 ⦄ (refl and (v1 and v2)) =
  reduce-valid (sub e1 (ctx-map σ)) _ {{r1}} (refl and v1) and reduce-valid (sub e2 (ctx-map σ)) _ {{r2}} (refl and v2)
reduce-valid (sub (sub e τ) σ) Γ ⦃ refl and-also r ⦄ (eq1 and (eq2 and v)) = reduce-valid (sub e (τ ⊚ σ)) Γ ⦃ r ⦄ (eq1 and v)

{-# TERMINATING #-}
reduce-sound : (e : Expr C) (Γ : Ctx C) {{v : IsValidCtx Γ e}} {{_ : Reducible e}} →
               interp-expr e Γ ≅ᵗʸ interp-expr (reduce e) Γ {{reduce-valid e Γ v}}
reduce-sound (con T) Γ = ≅ᵗʸ-refl
reduce-sound (nul U) Γ = ≅ᵗʸ-refl
reduce-sound (un F e) Γ = cong-un (reduce-sound e _)
reduce-sound (bin F e1 e2) Γ {{v1 and v2}} {{r1 and r2}} = cong-bin (reduce-sound e1 _ {{v1}} {{r1}})
                                                                    (reduce-sound e2 _ {{v2}} {{r2}})
reduce-sound (sub (con T) σ) Γ = ≅ᵗʸ-refl
reduce-sound (sub (nul U) σ) Γ ⦃ refl and _ ⦄ = natural-nul σ
reduce-sound (sub (un F e) σ) Γ ⦃ refl and v ⦄ = ≅ᵗʸ-trans (natural-un σ)
                                                           (cong-un (reduce-sound (sub e (ctx-map σ)) _ {{refl and v}}))
reduce-sound (sub (bin F e1 e2) σ) Γ ⦃ refl and (v1 and v2) ⦄ ⦃ r1 and r2 ⦄ =
  ≅ᵗʸ-trans (natural-bin σ)
            (cong-bin (reduce-sound (sub e1 (ctx-map σ)) _ {{_}} {{r1}})
                      (reduce-sound (sub e2 (ctx-map σ)) _ {{_}} {{r2}}))
reduce-sound (sub (sub e τ) σ) Γ ⦃ refl and (refl and v) ⦄ ⦃ refl and-also r ⦄ =
  ≅ᵗʸ-trans (ty-subst-comp (interp-expr e _ {{v}}) τ σ)
            (reduce-sound (sub e (τ ⊚ σ)) _ {{_}} {{r}})
