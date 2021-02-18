{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Naturality solver
--
-- This module implements a solver for proofs of type equalities making use
-- of naturality. A typical example for its applicability can be found in
-- Reflection.Examples.Naturality.
-- The solver works with arbitrary nullary, unary and binary type operations
-- that are natural with respect to the context (and that also respect equivalence
-- of types in case of unary and binary operations). When you implement a new
-- operation in a specific base category, you can make the solver work with it
-- by providing a value of the appropriate record type below (NullaryTypeOp,
-- UnaryTypeOp or BinaryTypeOp).
-- Note that we use the option omega-in-omega in order to define
-- an inductive data type in Setω and to pattern match on it (which
-- is not possible in Agda 2.6.1 without this option). This code should
-- typecheck without this option in Agda 2.6.2 once released.
--------------------------------------------------

module Reflection.Naturality.Solver where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl) renaming (subst to transp)

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.Helpers public
open import Reflection.Naturality.TypeOperations

private
  variable
    C D D' : Category


--------------------------------------------------
-- Definition of expressions that represent the structure of a type.

-- An expression is indexed by its skeleton, which drops the information
-- about contexts but keeps track of universe levels. The skeleton is needed
-- to convince Agda that the function reduce below terminates.
data ExprSkeleton : Set where
  scon : ExprSkeleton
  snul : ExprSkeleton
  sun  : ExprSkeleton → ExprSkeleton
  sbin : ExprSkeleton → ExprSkeleton → ExprSkeleton
  ssub : ExprSkeleton → ExprSkeleton

data Expr (Γ : Ctx C) : ExprSkeleton → Set₁ where
  con : (T : Ty Γ) → Expr Γ scon
  nul : (U : NullaryTypeOp C) → {{IsNullaryNatural U}} → Expr Γ snul
  un  : ∀ {s} {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} →
        (F : UnaryTypeOp Φ) → {{IsUnaryNatural F}} → (e : Expr (Φ Γ) s) → Expr Γ (sun s)
  bin : ∀ {s s'} {Φ : CtxOp C D} {Ψ : CtxOp C D'} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} →
        (F : BinaryTypeOp Φ Ψ) → {{IsBinaryNatural F}} → (e1 : Expr (Φ Γ) s) (e2 : Expr (Ψ Γ) s') → Expr Γ (sbin s s')
  sub : ∀ {s} {Δ : Ctx C} →
        Expr Δ s → (σ : Γ ⇒ Δ) → Expr Γ (ssub s)

⟦_⟧exp : ∀ {s} {Γ : Ctx C} → Expr Γ s → Ty Γ
⟦ con T ⟧exp = T
⟦ nul U ⟧exp = U
⟦ un F e ⟧exp = F ⟦ e ⟧exp
⟦ bin F e1 e2 ⟧exp = F ⟦ e1 ⟧exp ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]


--------------------------------------------------
-- Reduction of expressions + soundness

reduce-skeleton : ExprSkeleton → ExprSkeleton
reduce-skeleton scon = scon
reduce-skeleton snul = snul
reduce-skeleton (sun s) = sun (reduce-skeleton s)
reduce-skeleton (sbin s1 s2) = sbin (reduce-skeleton s1) (reduce-skeleton s2)
reduce-skeleton (ssub scon) = ssub scon
reduce-skeleton (ssub snul) = snul
reduce-skeleton (ssub (sun s)) = sun (reduce-skeleton (ssub s))
reduce-skeleton (ssub (sbin s1 s2)) = sbin (reduce-skeleton (ssub s1)) (reduce-skeleton (ssub s2))
reduce-skeleton (ssub (ssub s)) = reduce-skeleton (ssub s)

reduce : ∀ {s} {Γ : Ctx C} → Expr Γ s → Expr Γ (reduce-skeleton s)
reduce (con T) = con T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) = bin F (reduce e1) (reduce e2)
reduce (sub (con T) σ) = sub (con T) σ
reduce (sub (nul U) σ) = nul U
reduce (sub (un F e) σ) = un F (reduce (sub e (ctx-map σ)))
reduce (sub (bin F e1 e2) σ) = bin F (reduce (sub e1 (ctx-map σ))) (reduce (sub e2 (ctx-map σ)))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {s} {Γ : Ctx C} (e : Expr Γ s) →
               ⟦ e ⟧exp ≅ᵗʸ ⟦ reduce e ⟧exp
reduce-sound (con T) = ≅ᵗʸ-refl
reduce-sound (nul U) = ≅ᵗʸ-refl
reduce-sound (un F e) = cong-un (reduce-sound e)
reduce-sound (bin F e1 e2) = cong-bin (reduce-sound e1) (reduce-sound e2)
reduce-sound (sub (con T) σ) = ≅ᵗʸ-refl
reduce-sound (sub (nul U) σ) = natural-nul σ
reduce-sound (sub (un F e) σ) = ≅ᵗʸ-trans (natural-un σ) (cong-un (reduce-sound (sub e (ctx-map σ))))
{-
  begin
    (F ⟦ e ⟧exp) [ σ ]
  ≅⟨ natural-un σ ⟩
    F (⟦ e ⟧exp [ ctx-map σ ])
  ≅⟨⟩
    F ⟦ sub e (ctx-map σ) ⟧exp
  ≅⟨ cong-un (reduce-sound (sub e (ctx-map σ))) ⟩
    F ⟦ reduce (sub e (ctx-map σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
-}
reduce-sound (sub (bin F e1 e2) σ) = ≅ᵗʸ-trans (natural-bin σ) (cong-bin (reduce-sound (sub e1 (ctx-map σ)))
                                                                         (reduce-sound (sub e2 (ctx-map σ))))
{-
  begin
    (F ⟦ e1 ⟧exp ⟦ e2 ⟧exp) [ σ ]
  ≅⟨ natural-bin σ ⟩
    F (⟦ e1 ⟧exp [ ctx-map σ ]) (⟦ e2 ⟧exp [ ctx-map σ ])
  ≅⟨⟩
    F ⟦ sub e1 (ctx-map σ) ⟧exp ⟦ sub e2 (ctx-map σ) ⟧exp
  ≅⟨ cong-bin (reduce-sound (sub e1 (ctx-map σ))) (reduce-sound (sub e2 (ctx-map σ))) ⟩
    F ⟦ reduce (sub e1 (ctx-map σ)) ⟧exp ⟦ reduce (sub e2 (ctx-map σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
-}
reduce-sound (sub (sub e τ) σ) = ≅ᵗʸ-trans (ty-subst-comp ⟦ e ⟧exp τ σ) (reduce-sound (sub e (τ ⊚ σ)))
{-
  begin
    (⟦ e ⟧exp [ τ ]) [ σ ]
  ≅⟨ ty-subst-comp ⟦ e ⟧exp τ σ ⟩
    ⟦ e ⟧exp [ τ ⊚ σ ]
  ≅⟨⟩
    ⟦ sub e (τ ⊚ σ) ⟧exp
  ≅⟨ reduce-sound (sub e (τ ⊚ σ)) ⟩
    ⟦ reduce (sub e (τ ⊚ σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
-}

⟦⟧exp-cong : ∀ {s s'} {Γ : Ctx C} →
             {e : Expr Γ s} {e' : Expr Γ s'} →
             (p : s ≡ s') →
             transp (Expr Γ) p e ≡ e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl


--------------------------------------------------
-- End result

-- Not for pracical usage. Use the tactic by-naturality from Reflection.Tactic.Naturality instead.
type-naturality-reflect : ∀ {s s'} {Γ : Ctx C} →
                          (e : Expr Γ s) (e' : Expr Γ s') →
                          (p : reduce-skeleton s ≡ reduce-skeleton s') →
                          transp (Expr Γ) p (reduce e) ≡ reduce e' →
                          ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
type-naturality-reflect e e' p q =
  begin
    ⟦ e ⟧exp
  ≅⟨ reduce-sound e ⟩
    ⟦ reduce e ⟧exp
  ≅⟨ ⟦⟧exp-cong p q ⟩
    ⟦ reduce e' ⟧exp
  ≅˘⟨ reduce-sound e' ⟩
    ⟦ e' ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
