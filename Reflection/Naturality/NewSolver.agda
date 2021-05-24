module Reflection.Naturality.NewSolver where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong) renaming (subst to transp)

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.ContextFunctors
open import Reflection.Naturality.TypeOperations


private
  variable
    C D D' : Category

data Expr (C : Category) : Set₁ where
  con : (Γ : Ctx C) (T : Ty Γ) → Expr C
  nul : (U : NullaryTypeOp C) → {{IsNullaryNatural U}} → Expr C
  un  : {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} →
        (F : UnaryTypeOp Φ) → {{IsUnaryNatural F}} → (e : Expr D) → Expr C
  bin : {Φ : CtxOp C D} {Ψ : CtxOp C D'} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} →
        (F : BinaryTypeOp Φ Ψ) → {{IsBinaryNatural F}} → (e1 : Expr D) (e2 : Expr D') → Expr C
  sub : (e : Expr C) (Δ Γ : Ctx C) (σ : Δ ⇒ Γ) → Expr C

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

  and-also-instance : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {{a : A}} → {{B a}} → A AndAlso B
  and-also-instance {{a}} {{b}} = a and-also b

IsValidCtx : Ctx C → Expr C → Set₁
IsValidCtx Γ (con Δ T) = Γ ≡ Δ
IsValidCtx Γ (nul U) = ⊤
IsValidCtx Γ (un {Φ = Φ} F e) = IsValidCtx (Φ Γ) e
IsValidCtx Γ (bin {Φ = Φ} {Ψ = Ψ} F e1 e2) = (IsValidCtx (Φ Γ) e1) And (IsValidCtx (Ψ Γ) e2)
IsValidCtx Γ (sub e Δ Θ σ) = (Γ ≡ Δ) And (IsValidCtx Θ e)

interp-expr : (e : Expr C) (Γ : Ctx C) → {{IsValidCtx Γ e}} → Ty Γ
interp-expr (con _ T) Γ ⦃ refl ⦄ = T
interp-expr (nul U) Γ ⦃ v ⦄ = U
interp-expr (un {Φ = Φ} F e) Γ ⦃ v ⦄ = F (interp-expr e (Φ Γ))
interp-expr (bin {Φ = Φ} {Ψ = Ψ} F e1 e2) Γ ⦃ v1 and v2 ⦄ = F (interp-expr e1 (Φ Γ) {{v1}}) (interp-expr e2 (Ψ Γ) {{v2}})
interp-expr (sub e _ _ σ) Γ ⦃ refl and v ⦄ = (interp-expr e _ {{v}}) [ σ ]

{-# TERMINATING #-}
Reducible : Expr C → Set₁
Reducible (con _ T) = ⊤
Reducible (nul U) = ⊤
Reducible (un F e) = Reducible e
Reducible (bin F e1 e2) = Reducible e1 And Reducible e2
Reducible (sub (con _ T) _ _ σ) = ⊤
Reducible (sub (nul U) _ _ σ) = ⊤
Reducible (sub (un F e) _ _ σ) = Reducible (sub e _ _ (ctx-map σ))
Reducible (sub (bin F e1 e2) _ _ σ) = Reducible (sub e1 _ _ (ctx-map σ)) And Reducible (sub e2 _ _ (ctx-map σ))
Reducible (sub (sub e Δτ Γτ τ) Δσ Γσ σ) = (Γσ ≡ Δτ) AndAlso λ { refl → Reducible (sub e _ _ (τ ⊚ σ)) }

{-# TERMINATING #-}
reduce : (e : Expr C) → {{Reducible e}} → Expr C
reduce (con _ T) = con _ T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) {{ r1 and r2 }} = bin F (reduce e1 {{r1}}) (reduce e2 {{r2}})
reduce (sub (con _ T) _ _ σ) = sub (con _ T) _ _ σ
reduce (sub (nul U) _ _ σ) = nul U
reduce (sub (un F e) _ _ σ) = un F (reduce (sub e _ _ (ctx-map σ)))
reduce (sub (bin F e1 e2) _ _ σ) {{ r1 and r2 }} = bin F (reduce (sub e1 _ _ (ctx-map σ)) {{r1}}) (reduce (sub e2 _ _ (ctx-map σ)) {{r2}})
reduce (sub (sub e _ _ τ) _ _ σ) ⦃ refl and-also r ⦄ = reduce (sub e _ _ (τ ⊚ σ)) ⦃ r ⦄

{-# TERMINATING #-}
reduce-valid : (e : Expr C) (Γ : Ctx C) → {{_ : Reducible e}} →
               IsValidCtx Γ e → IsValidCtx Γ (reduce e)
reduce-valid (con _ T) Γ ⦃ r ⦄ v = v
reduce-valid (nul U) Γ ⦃ r ⦄ v = tt
reduce-valid (un {Φ = Φ} F e) Γ ⦃ r ⦄ v = reduce-valid e (Φ Γ) v
reduce-valid (bin F e1 e2) Γ ⦃ r1 and r2 ⦄ (v1 and v2) = reduce-valid e1 _ {{r1}} v1 and reduce-valid e2 _ {{r2}} v2
reduce-valid (sub (con _ T) _ _ σ) Γ ⦃ r ⦄ v = v
reduce-valid (sub (nul U) _ _ σ) Γ ⦃ r ⦄ v = tt
reduce-valid (sub (un F e) _ _ σ) Γ ⦃ r ⦄ (refl and v) = reduce-valid (sub e _ _ (ctx-map σ)) _ (refl and v)
reduce-valid (sub (bin F e1 e2) _ _ σ) Γ ⦃ r1 and r2 ⦄ (refl and (v1 and v2)) =
  reduce-valid (sub e1 _ _ (ctx-map σ)) _ {{r1}} (refl and v1) and reduce-valid (sub e2 _ _ (ctx-map σ)) _ {{r2}} (refl and v2)
reduce-valid (sub (sub e _ _ τ) _ _ σ) Γ ⦃ refl and-also r ⦄ (eq1 and (eq2 and v)) = reduce-valid (sub e _ _ (τ ⊚ σ)) Γ ⦃ r ⦄ (eq1 and v)

{-# TERMINATING #-}
reduce-sound : (e : Expr C) {Γ : Ctx C} {{v : IsValidCtx Γ e}} {{_ : Reducible e}} →
               interp-expr e Γ ≅ᵗʸ interp-expr (reduce e) Γ {{reduce-valid e Γ v}}
reduce-sound (con _ T) = ≅ᵗʸ-refl
reduce-sound (nul U) = ≅ᵗʸ-refl
reduce-sound (un F e) = cong-un (reduce-sound e)
reduce-sound (bin F e1 e2) {{v1 and v2}} {{r1 and r2}} = cong-bin (reduce-sound e1 {{v1}} {{r1}})
                                                                  (reduce-sound e2 {{v2}} {{r2}})
reduce-sound (sub (con _ T) _ _ σ) = ≅ᵗʸ-refl
reduce-sound (sub (nul U) _ _ σ) ⦃ refl and _ ⦄ = natural-nul σ
reduce-sound (sub (un F e) _ _ σ) ⦃ refl and v ⦄ = ≅ᵗʸ-trans (natural-un σ)
                                                         (cong-un (reduce-sound (sub e _ _ (ctx-map σ)) {{refl and v}}))
reduce-sound (sub (bin F e1 e2) _ _ σ) ⦃ refl and (v1 and v2) ⦄ ⦃ r1 and r2 ⦄ =
  ≅ᵗʸ-trans (natural-bin σ)
            (cong-bin (reduce-sound (sub e1 _ _ (ctx-map σ)) {{_}} {{r1}})
                      (reduce-sound (sub e2 _ _ (ctx-map σ)) {{_}} {{r2}}))
reduce-sound (sub (sub e _ _ τ) _ _ σ) ⦃ refl and (refl and v) ⦄ ⦃ refl and-also r ⦄ =
  ≅ᵗʸ-trans (ty-subst-comp (interp-expr e _ {{v}}) τ σ)
            (reduce-sound (sub e _ _ (τ ⊚ σ)) {{_}} {{r}})

interp-validity-irrelevant : (e : Expr C) (Γ : Ctx C) {{v1 v2 : IsValidCtx Γ e}} →
                             interp-expr e Γ {{v1}} ≅ᵗʸ interp-expr e Γ {{v2}}
interp-validity-irrelevant (con _ T) Γ ⦃ refl ⦄ ⦃ refl ⦄ = ≅ᵗʸ-refl
interp-validity-irrelevant (nul U) Γ ⦃ v1 ⦄ ⦃ v2 ⦄ = ≅ᵗʸ-refl
interp-validity-irrelevant (un F e) Γ ⦃ v1 ⦄ ⦃ v2 ⦄ = cong-un (interp-validity-irrelevant e _)
interp-validity-irrelevant (bin F e e') Γ ⦃ v1 and v1' ⦄ ⦃ v2 and v2' ⦄ = cong-bin (interp-validity-irrelevant e _ {{v1}} {{v2}})
                                                                                   (interp-validity-irrelevant e' _ {{v1'}} {{v2'}})
interp-validity-irrelevant (sub e _ _ σ) Γ ⦃ refl and v1 ⦄ ⦃ refl and v2 ⦄ = ty-subst-cong-ty σ (interp-validity-irrelevant e _ {{v1}} {{v2}})

interp-expr-cong : (e e' : Expr C) (Γ : Ctx C) →
                   {{_ : IsValidCtx Γ e}} {{_ : IsValidCtx Γ e'}} →
                   e ≡ e' →
                   interp-expr e Γ ≅ᵗʸ interp-expr e' Γ
interp-expr-cong e .e Γ refl = interp-validity-irrelevant e Γ

type-naturality-reflect : (e e' : Expr C) {Γ : Ctx C} →
                          {{_ : Reducible e}} {{_ : Reducible e'}} →
                          {{_ : IsValidCtx Γ e}} {{_ : IsValidCtx Γ e'}} →
                          reduce e ≡ reduce e' →
                          interp-expr e Γ ≅ᵗʸ interp-expr e' Γ
type-naturality-reflect e e' p =
  ≅ᵗʸ-trans (reduce-sound e)
            (≅ᵗʸ-trans (interp-expr-cong (reduce e) (reduce e') _ {{_}} {{_}} p)
                       (≅ᵗʸ-sym (reduce-sound e')))
