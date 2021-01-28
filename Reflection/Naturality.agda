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

module Reflection.Naturality where

open import Data.Vec.N-ary
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.Helpers public

private
  variable
    C D D' : Category


--------------------------------------------------
-- Definition of functors between context categories.

CtxOp : Category → Category → Setω
CtxOp C D = ∀ {ℓ r} → Ctx C ℓ r → Ctx D ℓ r

record IsCtxFunctor (Φ : CtxOp C D) : Setω where
  field
    ctx-map : ∀ {ℓ ℓ' r r'} {Δ : Ctx C ℓ r} {Γ : Ctx C ℓ' r'} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-id : ∀ {ℓ r} {Γ : Ctx C ℓ r} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : ∀ {ℓ ℓ' ℓ'' r r' r''} {Δ : Ctx C ℓ r} {Γ : Ctx C ℓ' r'}  {Θ : Ctx C ℓ'' r''} →
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

NullaryTypeOp : Category → Level → Level → Setω
NullaryTypeOp C ℓ r = ∀ {ℓc rc} {Γ : Ctx C ℓc rc} → Ty Γ ℓ r

record IsNullaryNatural {ℓ r} (U : NullaryTypeOp C ℓ r) : Setω where
  field
    natural-nul : ∀ {ℓc ℓc' rc rc'} {Δ : Ctx C ℓc rc} {Γ : Ctx C ℓc' rc'} (σ : Δ ⇒ Γ) →
                  U [ σ ] ≅ᵗʸ U

open IsNullaryNatural {{...}} public

UnaryTypeOp : CtxOp C D → (N-ary 4 Level Level) → (N-ary 4 Level Level) → Setω
UnaryTypeOp {C = C} Φ f g = ∀ {ℓc rc ℓt rt} {Γ : Ctx C ℓc rc} → Ty (Φ Γ) ℓt rt → Ty Γ (f ℓc rc ℓt rt) (g ℓc rc ℓt rt)

record IsUnaryNatural {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} {f g} (F : UnaryTypeOp Φ f g) : Setω where
  field
    natural-un : ∀ {ℓc ℓc' ℓt rc rc' rt} {Δ : Ctx C ℓc rc} {Γ : Ctx C ℓc' rc'} (σ : Δ ⇒ Γ) {T : Ty (Φ Γ) ℓt rt} →
                 (F T) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ])
    cong-un : ∀ {ℓc ℓt ℓt' rc rt rt'} {Γ : Ctx C ℓc rc}
              {T : Ty (Φ Γ) ℓt rt} {T' : Ty (Φ Γ) ℓt' rt'} →
              T ≅ᵗʸ T' → F T ≅ᵗʸ F T'

open IsUnaryNatural {{...}} public

BinaryTypeOp : CtxOp C D → CtxOp C D' → (N-ary 6 Level Level) → (N-ary 6 Level Level) → Setω
BinaryTypeOp {C = C} Φ Ψ f g = ∀ {ℓc ℓt ℓt' rc rt rt'} {Γ : Ctx C ℓc rc} →
                               Ty (Φ Γ) ℓt rt → Ty (Ψ Γ) ℓt' rt' → Ty Γ (f ℓc rc ℓt rt ℓt' rt') (g ℓc rc ℓt rt ℓt' rt')

record IsBinaryNatural
  {Φ : CtxOp C D} {Ψ : CtxOp C D'}
  {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}}
  {f g} (F : BinaryTypeOp Φ Ψ f g) : Setω where

  field
    natural-bin : ∀ {ℓc ℓc' ℓt ℓt' rc rc' rt rt'}
                  {Δ : Ctx C ℓc rc} {Γ : Ctx C ℓc' rc'} (σ : Δ ⇒ Γ) →
                  {T : Ty (Φ Γ) ℓt rt} {S : Ty (Ψ Γ) ℓt' rt'} →
                  (F T S) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ]) (S [ ctx-map σ ])
    cong-bin : ∀ {ℓc ℓt ℓt' ℓs ℓs' rc rt rt' rs rs'} {Γ : Ctx C ℓc rc}
               {T : Ty (Φ Γ) ℓt rt} {T' : Ty (Φ Γ) ℓt' rt'} {S : Ty (Ψ Γ) ℓs rs} {S' : Ty (Ψ Γ) ℓs' rs'} →
               T ≅ᵗʸ T' → S ≅ᵗʸ S' → F T S ≅ᵗʸ F T' S'

open IsBinaryNatural {{...}} public


--------------------------------------------------
-- Definition of expressions that represent the structure of a type.

-- An expression is indexed by its skeleton, which drops the information
-- about contexts but keeps track of universe levels. The skeleton is needed
-- to convince Agda that the function reduce below terminates.
data ExprSkeleton : Set where
  scon : Level → Level → ExprSkeleton
  snul : Level → Level → ExprSkeleton
  sun  : (f : N-ary 4 Level Level) (g : N-ary 4 Level Level) (ℓc rc : Level) →
         ExprSkeleton → ExprSkeleton
  sbin : (f : N-ary 6 Level Level) (g : N-ary 6 Level Level) (ℓc rc : Level) →
         ExprSkeleton → ExprSkeleton → ExprSkeleton
  ssub : (ℓc rc : Level) → ExprSkeleton → ExprSkeleton

level : ExprSkeleton → Level
rlevel : ExprSkeleton → Level

level (scon ℓ _) = ℓ
level (snul ℓ _) = ℓ
level (sun f _ ℓc rc s) = f ℓc rc (level s) (rlevel s)
level (sbin f _ ℓc rc s1 s2) = f ℓc rc (level s1) (rlevel s1) (level s2) (rlevel s2)
level (ssub _ _ s) = level s

rlevel (scon _ r) = r
rlevel (snul _ r) = r
rlevel (sun _ g ℓc rc s) = g ℓc rc (level s) (rlevel s)
rlevel (sbin _ g ℓc rc s1 s2) = g ℓc rc (level s1) (rlevel s1) (level s2) (rlevel s2)
rlevel (ssub _ _ s) = rlevel s


data Expr {ℓc rc : Level} (Γ : Ctx C ℓc rc) : ExprSkeleton → Setω where
  con : ∀ {ℓ r} → (T : Ty Γ ℓ r) → Expr Γ (scon ℓ r)
  nul : ∀ {ℓ r} →
        (U : NullaryTypeOp C ℓ r) → {{IsNullaryNatural U}} → Expr Γ (snul ℓ r)
  un  : ∀ {D f g s} {Φ : CtxOp C D} {{_ : IsCtxFunctor Φ}} →
        (F : UnaryTypeOp Φ f g) → {{IsUnaryNatural F}} → (e : Expr (Φ Γ) s) → Expr Γ (sun f g ℓc rc s)
  bin : ∀ {D D' f g s s'} {Φ : CtxOp C D} {Ψ : CtxOp C D'} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} →
        (F : BinaryTypeOp Φ Ψ f g) → {{IsBinaryNatural F}} → (e1 : Expr (Φ Γ) s) (e2 : Expr (Ψ Γ) s') → Expr Γ (sbin f g ℓc rc s s')
  sub : ∀ {ℓc' rc' s} {Δ : Ctx C ℓc' rc'} →
        Expr Δ s → (σ : Γ ⇒ Δ) → Expr Γ (ssub ℓc rc s)

⟦_⟧exp : ∀ {ℓc rc s} {Γ : Ctx C ℓc rc} → Expr Γ s → Ty Γ (level s) (rlevel s)
⟦ con T ⟧exp = T
⟦ nul U ⟧exp = U
⟦ un F e ⟧exp = F ⟦ e ⟧exp
⟦ bin F e1 e2 ⟧exp = F ⟦ e1 ⟧exp ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]


--------------------------------------------------
-- Reduction of expressions + soundness

reduce-skeleton : ExprSkeleton → ExprSkeleton
reduce-skeleton (scon ℓ r) = scon ℓ r
reduce-skeleton (snul ℓ r) = snul ℓ r
reduce-skeleton (sun f g ℓc rc s) = sun f g ℓc rc (reduce-skeleton s)
reduce-skeleton (sbin f g ℓc rc s1 s2) = sbin f g ℓc rc (reduce-skeleton s1) (reduce-skeleton s2)
reduce-skeleton (ssub ℓc rc (scon ℓ r)) = ssub ℓc rc (scon ℓ r)
reduce-skeleton (ssub ℓc rc (snul ℓ r)) = snul ℓ r
reduce-skeleton (ssub ℓc rc (sun f g ℓc' rc' s)) = sun f g ℓc rc (reduce-skeleton (ssub ℓc rc s))
reduce-skeleton (ssub ℓc rc (sbin f g ℓc' rc' s1 s2)) = sbin f g ℓc rc (reduce-skeleton (ssub ℓc rc s1))
                                                                       (reduce-skeleton (ssub ℓc rc s2))
reduce-skeleton (ssub ℓc rc (ssub ℓc' rc' s)) = reduce-skeleton (ssub ℓc rc s)

reduce : ∀ {ℓc rc s} {Γ : Ctx C ℓc rc} → Expr Γ s → Expr Γ (reduce-skeleton s)
reduce (con T) = con T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) = bin F (reduce e1) (reduce e2)
reduce (sub (con T) σ) = sub (con T) σ
reduce (sub (nul U) σ) = nul U
reduce (sub (un F e) σ) = un F (reduce (sub e (ctx-map σ)))
reduce (sub (bin F e1 e2) σ) = bin F (reduce (sub e1 (ctx-map σ))) (reduce (sub e2 (ctx-map σ)))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {ℓc rc s} {Γ : Ctx C ℓc rc} (e : Expr Γ s) →
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

⟦⟧exp-cong : ∀ {ℓc rc s s'} {Γ : Ctx C ℓc rc} →
             {e : Expr Γ s} {e' : Expr Γ s'} →
             (p : s ≡ s') →
             ω-transp (Expr Γ) p e ≡ω e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl


--------------------------------------------------
-- End result

-- Not for pracical usage. Use the tactic by-naturality from Reflection.Tactic.Naturality instead.
type-naturality-reflect : ∀ {ℓc rc s s'} {Γ : Ctx C ℓc rc} →
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
