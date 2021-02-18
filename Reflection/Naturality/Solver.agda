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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
  scon : Level → ExprSkeleton
  snul : (f : Level → Level) (ℓc : Level) → ExprSkeleton
  sun  : (f : Level → Level → Level) (ℓc : Level) →
         ExprSkeleton → ExprSkeleton
  sbin : (f : Level → Level → Level → Level) (ℓc : Level) →
         ExprSkeleton → ExprSkeleton → ExprSkeleton
  ssub : (ℓc : Level) → ExprSkeleton → ExprSkeleton

level : ExprSkeleton → Level
level (scon ℓ) = ℓ
level (snul f ℓc) = f ℓc
level (sun f ℓc s) = f ℓc (level s)
level (sbin f ℓc s1 s2) = f ℓc (level s1) (level s2)
level (ssub ℓc s) = level s

data Expr {ℓc : Level} (Γ : Ctx C ℓc) : ExprSkeleton → Setω where
  con : ∀ {ℓ} → (T : Ty Γ ℓ) → Expr Γ (scon ℓ)
  nul : ∀ {f} →
        (U : NullaryTypeOp C f) → {{IsNullaryNatural U}} → Expr Γ (snul f ℓc)
  un  : ∀ {D f s} {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} →
        (F : UnaryTypeOp Φ f) → {{IsUnaryNatural F}} → (e : Expr (Φ Γ) s) → Expr Γ (sun f ℓc s)
  bin : ∀ {D D' f s s'} {Φ : CtxOp C D} {Ψ : CtxOp C D'} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} →
        (F : BinaryTypeOp Φ Ψ f) → {{IsBinaryNatural F}} → (e1 : Expr (Φ Γ) s) (e2 : Expr (Ψ Γ) s') → Expr Γ (sbin f ℓc s s')
  sub : ∀ {ℓc' s} {Δ : Ctx C ℓc'} →
        Expr Δ s → (σ : Γ ⇒ Δ) → Expr Γ (ssub ℓc s)

⟦_⟧exp : ∀ {ℓc s} {Γ : Ctx C ℓc} → Expr Γ s → Ty Γ (level s)
⟦ con T ⟧exp = T
⟦ nul U ⟧exp = U
⟦ un F e ⟧exp = F ⟦ e ⟧exp
⟦ bin F e1 e2 ⟧exp = F ⟦ e1 ⟧exp ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]


--------------------------------------------------
-- Reduction of expressions + soundness

reduce-skeleton : ExprSkeleton → ExprSkeleton
reduce-skeleton (scon ℓ) = scon ℓ
reduce-skeleton (snul f ℓc) = snul f ℓc
reduce-skeleton (sun f ℓc s) = sun f ℓc (reduce-skeleton s)
reduce-skeleton (sbin f ℓc s1 s2) = sbin f ℓc (reduce-skeleton s1) (reduce-skeleton s2)
reduce-skeleton (ssub ℓc (scon ℓ)) = ssub ℓc (scon ℓ)
reduce-skeleton (ssub ℓc (snul f ℓc')) = snul f ℓc
reduce-skeleton (ssub ℓc (sun f ℓc' s)) = sun f ℓc (reduce-skeleton (ssub ℓc s))
reduce-skeleton (ssub ℓc (sbin f ℓc' s1 s2)) = sbin f ℓc (reduce-skeleton (ssub ℓc s1)) (reduce-skeleton (ssub ℓc s2))
reduce-skeleton (ssub ℓc (ssub ℓc' s)) = reduce-skeleton (ssub ℓc s)

reduce : ∀ {ℓc s} {Γ : Ctx C ℓc} → Expr Γ s → Expr Γ (reduce-skeleton s)
reduce (con T) = con T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) = bin F (reduce e1) (reduce e2)
reduce (sub (con T) σ) = sub (con T) σ
reduce (sub (nul U) σ) = nul U
reduce (sub (un F e) σ) = un F (reduce (sub e (ctx-map σ)))
reduce (sub (bin F e1 e2) σ) = bin F (reduce (sub e1 (ctx-map σ))) (reduce (sub e2 (ctx-map σ)))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {ℓc s} {Γ : Ctx C ℓc} (e : Expr Γ s) →
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

⟦⟧exp-cong : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
             {e : Expr Γ s} {e' : Expr Γ s'} →
             (p : s ≡ s') →
             ω-transp (Expr Γ) p e ≡ω e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl


--------------------------------------------------
-- End result

-- Not for pracical usage. Use the tactic by-naturality from Reflection.Tactic.Naturality instead.
type-naturality-reflect : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
                          (e : Expr Γ s) (e' : Expr Γ s') →
                          (p : reduce-skeleton s ≡ reduce-skeleton s') →
                          ω-transp (Expr Γ) p (reduce e) ≡ω reduce e' →
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
