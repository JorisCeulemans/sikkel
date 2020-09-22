{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Naturality solver
--
-- This module implements a solver for proofs of type equalities making use
-- of naturality. A typical example for its applicability can be found at the
-- bottom of the file.
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

open import Categories

module Reflection.Naturality {C : Category} where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.Helpers public


-- TODO: Allow operations that can change the context the type lives in using a certain endofunctor
-- on the category of contexts (needed for ▻). Later, functors between different categories might as well be interesting.

CtxOp : Setω
CtxOp = ∀ {ℓ} → Ctx C ℓ → Ctx C ℓ

record IsCtxFunctor (Φ : CtxOp) : Setω where
  field
    ctx-map : ∀ {ℓ ℓ'} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} → Δ ⇒ Γ → Φ Δ ⇒ Φ Γ
    ctx-map-id : ∀ {ℓ} {Γ : Ctx C ℓ} → ctx-map (id-subst Γ) ≅ˢ id-subst (Φ Γ)
    ctx-map-⊚ : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'}  {Θ : Ctx C ℓ''} →
                 (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 ctx-map (τ ⊚ σ) ≅ˢ ctx-map τ ⊚ ctx-map σ

open IsCtxFunctor {{...}} public

instance
  id-ctx-functor : IsCtxFunctor (λ Γ → Γ)
  ctx-map {{id-ctx-functor}} σ = σ
  ctx-map-id {{id-ctx-functor}} = ≅ˢ-refl
  ctx-map-⊚ {{id-ctx-functor}} _ _ = ≅ˢ-refl


--------------------------------------------------
-- Definition of record types of nullary, unary and binary type operations.

NullaryTypeOp : Level → Setω
NullaryTypeOp ℓ = ∀ {ℓc} {Γ : Ctx C ℓc} → Ty Γ ℓ

record IsNullaryNatural {ℓ} (U : NullaryTypeOp ℓ) : Setω where
  field
    natural-nul : ∀ {ℓc ℓc'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                  U [ σ ] ≅ᵗʸ U

open IsNullaryNatural {{...}} public

UnaryTypeOp : CtxOp → (Level → Level → Level) → Setω
UnaryTypeOp Φ f = ∀ {ℓc ℓt} {Γ : Ctx C ℓc} → Ty (Φ Γ) ℓt → Ty Γ (f ℓc ℓt)

record IsUnaryNatural {Φ : CtxOp} {{_ : IsCtxFunctor Φ}} {f} (F : UnaryTypeOp Φ f) : Setω where
  field
    natural-un : ∀ {ℓc ℓc' ℓt} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) {T : Ty (Φ Γ) ℓt} →
                 (F T) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ])
    cong-un : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc}
              {T : Ty (Φ Γ) ℓt} {T' : Ty (Φ Γ) ℓt'} →
              T ≅ᵗʸ T' → F T ≅ᵗʸ F T'

open IsUnaryNatural {{...}} public

BinaryTypeOp : CtxOp → CtxOp → (Level → Level → Level → Level) → Setω
BinaryTypeOp Φ Ψ f = ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc} → Ty (Φ Γ) ℓt → Ty (Ψ Γ) ℓt' → Ty Γ (f ℓc ℓt ℓt')

record IsBinaryNatural {Φ Ψ : CtxOp} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} {f} (F : BinaryTypeOp Φ Ψ f) : Setω where
  field
    natural-bin : ∀ {ℓc ℓc' ℓt ℓt'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                  {T : Ty (Φ Γ) ℓt} {S : Ty (Ψ Γ) ℓt'} →
                  (F T S) [ σ ] ≅ᵗʸ F (T [ ctx-map σ ]) (S [ ctx-map σ ])
    cong-bin : ∀ {ℓc ℓt ℓt' ℓs ℓs'} {Γ : Ctx C ℓc}
               {T : Ty (Φ Γ) ℓt} {T' : Ty (Φ Γ) ℓt'} {S : Ty (Ψ Γ) ℓs} {S' : Ty (Ψ Γ) ℓs'} →
               T ≅ᵗʸ T' → S ≅ᵗʸ S' → F T S ≅ᵗʸ F T' S'

open IsBinaryNatural {{...}} public


--------------------------------------------------
-- Definition of expressions that represent the structure of a type.

-- An expression is indexed by its skeleton, which drops the information
-- about contexts but keeps track of universe levels. The skeleton is needed
-- to convince Agda that the function reduce below terminates.
data ExpSkeleton : Set where
  scon : Level → ExpSkeleton
  snul : Level → ExpSkeleton
  sun  : (f : Level → Level → Level) (ℓc : Level) →
         ExpSkeleton → ExpSkeleton
  sbin : (f : Level → Level → Level → Level) (ℓc : Level) →
         ExpSkeleton → ExpSkeleton → ExpSkeleton
  ssub : (ℓc : Level) → ExpSkeleton → ExpSkeleton

level : ExpSkeleton → Level
level (scon ℓ) = ℓ
level (snul ℓ) = ℓ
level (sun f ℓc s) = f ℓc (level s)
level (sbin f ℓc s1 s2) = f ℓc (level s1) (level s2)
level (ssub ℓc s) = level s

data Exp : {ℓc : Level} (Γ : Ctx C ℓc) → ExpSkeleton → Setω where
  con : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        (T : Ty Γ ℓ) → Exp Γ (scon ℓ)
  nul : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        (U : NullaryTypeOp ℓ) → {{IsNullaryNatural U}} → Exp Γ (snul ℓ)
  un  : ∀ {ℓc f s} {Φ : CtxOp} {{_ : IsCtxFunctor Φ}} {Γ : Ctx C ℓc} →
        (F : UnaryTypeOp Φ f) → {{IsUnaryNatural F}} → (e : Exp (Φ Γ) s) → Exp Γ (sun f ℓc s)
  bin : ∀ {ℓc f s s'} {Φ Ψ : CtxOp} {{_ : IsCtxFunctor Φ}} {{_ : IsCtxFunctor Ψ}} {Γ : Ctx C ℓc} →
        (F : BinaryTypeOp Φ Ψ f) → {{IsBinaryNatural F}} → (e1 : Exp (Φ Γ) s) (e2 : Exp (Ψ Γ) s') → Exp Γ (sbin f ℓc s s')
  sub : ∀ {ℓc ℓc' s} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} →
        Exp Γ s → (σ : Δ ⇒ Γ) → Exp Δ (ssub ℓc s)

⟦_⟧exp : ∀ {ℓc s} {Γ : Ctx C ℓc} → Exp Γ s → Ty Γ (level s)
⟦ con T ⟧exp = T
⟦ nul U ⟧exp = U
⟦ un F e ⟧exp = F ⟦ e ⟧exp
⟦ bin F e1 e2 ⟧exp = F ⟦ e1 ⟧exp ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]


--------------------------------------------------
-- Reduction of expressions + soundness

reduce-skeleton : ExpSkeleton → ExpSkeleton
reduce-skeleton (scon ℓ) = scon ℓ
reduce-skeleton (snul ℓ) = snul ℓ
reduce-skeleton (sun f ℓc s) = sun f ℓc (reduce-skeleton s)
reduce-skeleton (sbin f ℓc s1 s2) = sbin f ℓc (reduce-skeleton s1) (reduce-skeleton s2)
reduce-skeleton (ssub ℓc (scon ℓ)) = ssub ℓc (scon ℓ)
reduce-skeleton (ssub ℓc (snul ℓ)) = snul ℓ
reduce-skeleton (ssub ℓc (sun f ℓc' s)) = sun f ℓc (reduce-skeleton (ssub ℓc s))
reduce-skeleton (ssub ℓc (sbin f ℓc' s1 s2)) = sbin f ℓc (reduce-skeleton (ssub ℓc s1)) (reduce-skeleton (ssub ℓc s2))
reduce-skeleton (ssub ℓc (ssub ℓc' s)) = reduce-skeleton (ssub ℓc s)

reduce : ∀ {ℓc s} {Γ : Ctx C ℓc} → Exp Γ s → Exp Γ (reduce-skeleton s)
reduce (con T) = con T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) = bin F (reduce e1) (reduce e2)
reduce (sub (con T) σ) = sub (con T) σ
reduce (sub (nul U) σ) = nul U
reduce (sub (un F e) σ) = un F (reduce (sub e (ctx-map σ)))
reduce (sub (bin F e1 e2) σ) = bin F (reduce (sub e1 (ctx-map σ))) (reduce (sub e2 (ctx-map σ)))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {ℓc s} {Γ : Ctx C ℓc} (e : Exp Γ s) →
               ⟦ e ⟧exp ≅ᵗʸ ⟦ reduce e ⟧exp
reduce-sound (con T) = ≅ᵗʸ-refl
reduce-sound (nul U) = ≅ᵗʸ-refl
reduce-sound (un F e) = cong-un (reduce-sound e)
reduce-sound (bin F e1 e2) = cong-bin (reduce-sound e1) (reduce-sound e2)
reduce-sound (sub (con T) σ) = ≅ᵗʸ-refl
reduce-sound (sub (nul U) σ) = natural-nul σ
reduce-sound (sub (un F e) σ) =
  begin
    (F ⟦ e ⟧exp) [ σ ]
  ≅⟨ natural-un σ ⟩
    F (⟦ e ⟧exp [ ctx-map σ ])
  ≅⟨⟩
    F ⟦ sub e (ctx-map σ) ⟧exp
  ≅⟨ cong-un (reduce-sound (sub e (ctx-map σ))) ⟩
    F ⟦ reduce (sub e (ctx-map σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
reduce-sound (sub (bin F e1 e2) σ) =
  begin
    (F ⟦ e1 ⟧exp ⟦ e2 ⟧exp) [ σ ]
  ≅⟨ natural-bin σ ⟩
    F (⟦ e1 ⟧exp [ ctx-map σ ]) (⟦ e2 ⟧exp [ ctx-map σ ])
  ≅⟨⟩
    F ⟦ sub e1 (ctx-map σ) ⟧exp ⟦ sub e2 (ctx-map σ) ⟧exp
  ≅⟨ cong-bin (reduce-sound (sub e1 (ctx-map σ))) (reduce-sound (sub e2 (ctx-map σ))) ⟩
    F ⟦ reduce (sub e1 (ctx-map σ)) ⟧exp ⟦ reduce (sub e2 (ctx-map σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
reduce-sound (sub (sub e τ) σ) =
  begin
    (⟦ e ⟧exp [ τ ]) [ σ ]
  ≅⟨ ty-subst-comp ⟦ e ⟧exp τ σ ⟩
    ⟦ e ⟧exp [ τ ⊚ σ ]
  ≅⟨⟩
    ⟦ sub e (τ ⊚ σ) ⟧exp
  ≅⟨ reduce-sound (sub e (τ ⊚ σ)) ⟩
    ⟦ reduce (sub e (τ ⊚ σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning

⟦⟧exp-cong : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
             {e : Exp Γ s} {e' : Exp Γ s'} →
             (p : s ≡ s') →
             ω-transp (Exp Γ) p e ≡ω e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl


--------------------------------------------------
-- End result

type-naturality-reflect : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
                          (e : Exp Γ s) (e' : Exp Γ s') →
                          (p : reduce-skeleton s ≡ reduce-skeleton s') →
                          ω-transp (Exp Γ) p (reduce e) ≡ω reduce e' →
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


--------------------------------------------------
-- Definition of some operations that exist in any presheaf category

module Operations where
  open import Types.Discrete
  open import Types.Functions
  open import Types.Products
  open import Types.Sums

  instance
    discr-nul : ∀ {ℓ} {A : Set ℓ} → IsNullaryNatural (Discr A)
    natural-nul {{discr-nul {A = A}}} σ = Discr-natural A σ

    fun-bin : IsBinaryNatural _⇛_
    natural-bin {{fun-bin}} σ = ⇛-natural σ
    cong-bin {{fun-bin}} = ⇛-cong

    prod-bin : IsBinaryNatural _⊠_
    natural-bin {{prod-bin}} σ = ⊠-natural σ
    cong-bin {{prod-bin}} = ⊠-cong

    sum-bin : IsBinaryNatural _⊞_
    natural-bin {{sum-bin}} σ = ⊞-natural σ
    cong-bin {{sum-bin}} = ⊞-cong

open Operations public

private
  open import Types.Discrete
  open import Types.Functions
  open import Types.Products

  example : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
            (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
            ((Bool' ⇛ Bool') ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
  example σ τ = type-naturality-reflect (sub (bin _⊠_ (bin _⇛_ (nul Bool') (nul Bool')) (sub (nul Bool') τ)) σ)
                                        (bin _⊠_ (sub (bin _⇛_ (nul Bool') (nul Bool')) σ) (nul Bool'))
                                        refl
                                        refl
