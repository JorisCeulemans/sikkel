{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Reflection for type equality
--
-- This module provides proof by reflection for equalities of types (in the topos of trees) on which
-- operations are applied (currently supported operations are substitutions and the later modality).
-- The problem is represented as a sequence of operations (TypeOpSeq) keeping track of the
-- context each type lives in. The reduction strategy is then to move "later" operations to the back
-- of the sequence (which are applied last) and subsequently group all substitutions in front in one
-- sequence of substitutions.
--------------------------------------------------

open import Categories
module Reflection.Types where

open import Level

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import GuardedRecursion.Later
open import Reflection.Helpers

infixr 5 _∷_

private
  variable
    ℓ ℓ' : Level
    Δ Γ Θ : Ctx ω ℓ


--------------------------------------------------
-- Syntax + semantics for operations on types

-- A value of TypeOp Γ Δ represents an operation that transforms a type in
-- context Γ into a type in context Δ
data TypeOp : Ctx ω ℓ → Ctx ω ℓ' → Setω where
  subst : (σ : Δ ⇒ Γ) → TypeOp Γ Δ
  later : TypeOp (◄ Γ) Γ

_⟦_⟧op : Ty Γ ℓ → TypeOp Γ Δ → Ty Δ ℓ
T ⟦ subst σ ⟧op = T [ σ ]
T ⟦ later   ⟧op = ▻ T

op-cong : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} (op : TypeOp Γ Δ) →
          T ≅ᵗʸ S → T ⟦ op ⟧op ≅ᵗʸ S ⟦ op ⟧op
op-cong (subst σ) eq = ty-subst-cong-ty σ eq
op-cong later     eq = ▻-cong eq

◄-op : TypeOp Γ Δ → TypeOp (◄ Γ) (◄ Δ)
◄-op (subst σ) = subst (◄-subst σ)
◄-op later     = later


--------------------------------------------------
-- Sequences of type operations (keeping track of the context)

data TypeOpSeq : Ctx ω ℓ → Ctx ω ℓ' → Setω where
  [] : TypeOpSeq Γ Γ
  _∷_ : TypeOp Γ Δ → TypeOpSeq Δ Θ → TypeOpSeq Γ Θ

_⟦_⟧ops : Ty Γ ℓ → TypeOpSeq Γ Δ → Ty Δ ℓ
T ⟦ []       ⟧ops = T
T ⟦ op ∷ seq ⟧ops = (T ⟦ op ⟧op) ⟦ seq ⟧ops

ops-cong : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} (seq : TypeOpSeq Γ Δ) →
           T ≅ᵗʸ S → T ⟦ seq ⟧ops ≅ᵗʸ S ⟦ seq ⟧ops
ops-cong []         eq = eq
ops-cong (op ∷ seq) eq = ops-cong seq (op-cong op eq)

◄-opseq : TypeOpSeq Γ Δ → TypeOpSeq (◄ Γ) (◄ Δ)
◄-opseq []         = []
◄-opseq (op ∷ seq) = ◄-op op ∷ ◄-opseq seq


--------------------------------------------------
-- First phase of reduction: moving all later operations to the back,
-- i.e. to the outside when applied on a type

_∷ʳ_ : TypeOpSeq Γ Δ → TypeOp Δ Θ → TypeOpSeq Γ Θ
[]          ∷ʳ op  = op ∷ []
(op1 ∷ seq) ∷ʳ op2 = op1 ∷ (seq ∷ʳ op2)

defer-later : TypeOpSeq Γ Δ → TypeOpSeq Γ Δ
defer-later []              = []
defer-later (subst σ ∷ seq) = subst σ ∷ defer-later seq
defer-later (later   ∷ seq) = ◄-opseq (defer-later seq) ∷ʳ later


--------------------------------------------------
-- Proving soundness of the first reduction step

snoc-denote : (T : Ty Γ ℓ) (seq : TypeOpSeq Γ Δ) (op : TypeOp Δ Θ) →
              T ⟦ seq ∷ʳ op ⟧ops ≅ᵗʸ (T ⟦ seq ⟧ops) ⟦ op ⟧op
snoc-denote T []          op  = ≅ᵗʸ-refl
snoc-denote T (op1 ∷ seq) op2 = snoc-denote (T ⟦ op1 ⟧op) seq op2

▻-op-commute : (T : Ty (◄ Γ) ℓ) (op : TypeOp Γ Δ) →
                ▻ (T ⟦ ◄-op op ⟧op) ≅ᵗʸ (▻ T) ⟦ op ⟧op
▻-op-commute T (subst σ) = ≅ᵗʸ-sym (▻-natural σ)
▻-op-commute T later     = ≅ᵗʸ-refl

▻-ops-commute : (T : Ty (◄ Γ) ℓ) (seq : TypeOpSeq Γ Δ) →
                 ▻ (T ⟦ ◄-opseq seq ⟧ops) ≅ᵗʸ (▻ T) ⟦ seq ⟧ops
▻-ops-commute T []         = ≅ᵗʸ-refl
▻-ops-commute T (op ∷ seq) = ≅ᵗʸ-trans (▻-ops-commute (T ⟦ ◄-op op ⟧op) seq)
                                       (ops-cong seq (▻-op-commute T op))

defer-sound : (T : Ty Γ ℓ) (seq : TypeOpSeq Γ Δ) →
              T ⟦ defer-later seq ⟧ops ≅ᵗʸ T ⟦ seq ⟧ops
defer-sound T []              = ≅ᵗʸ-refl
defer-sound T (subst σ ∷ seq) = defer-sound (T [ σ ]) seq
defer-sound T (later   ∷ seq) =
  begin
    T ⟦ ◄-opseq (defer-later seq) ∷ʳ later ⟧ops
  ≅⟨ snoc-denote T (◄-opseq (defer-later seq)) later ⟩
    ▻ (T ⟦ ◄-opseq (defer-later seq) ⟧ops)
  ≅⟨ ▻-ops-commute T (defer-later seq) ⟩
    (▻ T) ⟦ defer-later seq ⟧ops
  ≅⟨ defer-sound (▻ T) seq ⟩
    (▻ T) ⟦ seq ⟧ops ∎
  where open ≅ᵗʸ-Reasoning

-- The following is superseded by type-reflect (see further).
type-reflect' : {T : Ty Γ ℓ} (seq seq' : TypeOpSeq Γ Δ) →
                T ⟦ defer-later seq ⟧ops ≅ᵗʸ T ⟦ defer-later seq' ⟧ops →
                T ⟦ seq ⟧ops ≅ᵗʸ T ⟦ seq' ⟧ops
type-reflect' {T = T} seq seq' eq =
  begin
    T ⟦ seq ⟧ops
  ≅˘⟨ defer-sound T seq ⟩
    T ⟦ defer-later seq ⟧ops
  ≅⟨ eq ⟩
    T ⟦ defer-later seq' ⟧ops
  ≅⟨ defer-sound T seq' ⟩
    T ⟦ seq' ⟧ops ∎
  where open ≅ᵗʸ-Reasoning


--------------------------------------------------
-- Second reduction step: grouping substitutions

-- Same definitions as in CwF-Structure.SubstitutionSequence
data SubstSeq : Ctx ω ℓ → Ctx ω ℓ' → Setω where
  _◼ : (σ : Δ ⇒ Γ) → SubstSeq Δ Γ
  _∷_ : (σ : Γ ⇒ Θ) (σs : SubstSeq Δ Γ) → SubstSeq Δ Θ

fold : SubstSeq Δ Γ → Δ ⇒ Γ
fold (σ ◼)    = σ
fold (σ ∷ σs) = σ ⊚ fold σs

-- This looks very similar to TypeOp but uses substitution sequences instead of
-- individual substitutions.
data STypeOp : Ctx ω ℓ → Ctx ω ℓ' → Setω where
  subseq : (σs : SubstSeq Δ Γ) → STypeOp Γ Δ
  later  : STypeOp (◄ Γ) Γ

_⟦_⟧sop : Ty Γ ℓ → STypeOp Γ Δ → Ty Δ ℓ
T ⟦ subseq σs ⟧sop = T [ fold σs ]
T ⟦ later     ⟧sop = ▻ T

sop-cong : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} (sop : STypeOp Γ Δ) →
           T ≅ᵗʸ S → T ⟦ sop ⟧sop ≅ᵗʸ S ⟦ sop ⟧sop
sop-cong (subseq σs) eq = ty-subst-cong-ty (fold σs) eq
sop-cong later       eq = ▻-cong eq

data STypeOpSeq : Ctx ω ℓ → Ctx ω ℓ' → Setω where
  []  : STypeOpSeq Γ Γ
  _∷_ : STypeOp Γ Δ → STypeOpSeq Δ Θ → STypeOpSeq Γ Θ

_⟦_⟧sops : Ty Γ ℓ → STypeOpSeq Γ Δ → Ty Δ ℓ
T ⟦ []        ⟧sops = T
T ⟦ sop ∷ seq ⟧sops = (T ⟦ sop ⟧sop) ⟦ seq ⟧sops

sops-cong : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} (seq : STypeOpSeq Γ Δ) →
            T ≅ᵗʸ S → T ⟦ seq ⟧sops ≅ᵗʸ S ⟦ seq ⟧sops
sops-cong []          eq = eq
sops-cong (sop ∷ seq) eq = sops-cong seq (sop-cong sop eq)

_ˢ∷_ : Δ ⇒ Γ → STypeOpSeq Δ Θ → STypeOpSeq Γ Θ
σ ˢ∷ (subseq σs ∷ seq) = subseq (σ ∷ σs) ∷ seq
σ ˢ∷ seq               = subseq (σ ◼) ∷ seq

-- The actual reduction step
group-subst : TypeOpSeq Γ Δ → STypeOpSeq Γ Δ
group-subst []              = []
group-subst (subst σ ∷ seq) = σ ˢ∷ group-subst seq
group-subst (later   ∷ seq) = later ∷ group-subst seq


--------------------------------------------------
-- Proving soundness of the second reduction step

cons-subst-denote : (σ : Δ ⇒ Γ) (seq : STypeOpSeq Δ Θ) (T : Ty Γ ℓ) →
                    T ⟦ σ ˢ∷ seq ⟧sops ≅ᵗʸ (T [ σ ]) ⟦ seq ⟧sops
cons-subst-denote σ []                T = ≅ᵗʸ-refl
cons-subst-denote σ (subseq τs ∷ seq) T = sops-cong seq (≅ᵗʸ-sym (ty-subst-comp T σ (fold τs)))
cons-subst-denote σ (later     ∷ seq) T = ≅ᵗʸ-refl

group-subst-sound : (T : Ty Γ ℓ) (seq : TypeOpSeq Γ Δ) →
                    T ⟦ group-subst seq ⟧sops ≅ᵗʸ T ⟦ seq ⟧ops
group-subst-sound T []              = ≅ᵗʸ-refl
group-subst-sound T (subst σ ∷ seq) =
  begin
    T ⟦ σ ˢ∷ group-subst seq ⟧sops
  ≅⟨ cons-subst-denote σ (group-subst seq) T ⟩
    (T [ σ ]) ⟦ group-subst seq ⟧sops
  ≅⟨ group-subst-sound (T [ σ ]) seq ⟩
    (T [ σ ]) ⟦ seq ⟧ops ∎
  where open ≅ᵗʸ-Reasoning
group-subst-sound T (later   ∷ seq) = group-subst-sound (▻ T) seq

type-reflect : {T : Ty Γ ℓ} (seq seq' : TypeOpSeq Γ Δ) →
              T ⟦ group-subst (defer-later seq) ⟧sops ≅ᵗʸ T ⟦ group-subst (defer-later seq') ⟧sops →
              T ⟦ seq ⟧ops ≅ᵗʸ T ⟦ seq' ⟧ops
type-reflect {T = T} seq seq' eq =
  begin
    T ⟦ seq ⟧ops
  ≅˘⟨ defer-sound T seq ⟩
    T ⟦ defer-later seq ⟧ops
  ≅˘⟨ group-subst-sound T (defer-later seq) ⟩
    T ⟦ group-subst (defer-later seq) ⟧sops
  ≅⟨ eq ⟩
    T ⟦ group-subst (defer-later seq') ⟧sops
  ≅⟨ group-subst-sound T (defer-later seq') ⟩
    T ⟦ defer-later seq' ⟧ops
  ≅⟨ defer-sound T seq' ⟩
    T ⟦ seq' ⟧ops ∎
  where open ≅ᵗʸ-Reasoning

private
  module Examples (σ : Δ ⇒ Γ) (τ : ◄ Γ ⇒ ◄ Θ) where
    open import Types.Discrete
    open import CwF-Structure.SubstitutionSequence
    open import CwF-Structure.Terms

    example' : (▻ ((▻ Bool') [ τ ])) [ σ ] ≅ᵗʸ ▻ (▻ Bool')
    example' = type-reflect' (subst (!◇ (◄ (◄ Θ))) ∷ later ∷ subst τ ∷ later ∷ subst σ ∷ [])
                             (subst (!◇ (◄ (◄ Δ))) ∷ later ∷ later ∷ [])
                             (▻-cong (▻-cong (ty-subst-seq-cong (!◇ (◄ (◄ Θ)) ∷ ◄-subst τ ∷ ◄-subst (◄-subst σ) ◼)
                                                                  (!◇ (◄ (◄ Δ)) ◼)
                                                                  _
                                                                  (◇-terminal _ _ _))))

    example : (▻ ((▻ Bool') [ τ ])) [ σ ] ≅ᵗʸ ▻ (▻ Bool')
    example = type-reflect (subst (!◇ (◄ (◄ Θ))) ∷ later ∷ subst τ ∷ later ∷ subst σ ∷ [])
                           (subst (!◇ (◄ (◄ Δ))) ∷ later ∷ later ∷ [])
                           (▻-cong (▻-cong (ty-subst-cong-subst (◇-terminal _ _ _) _)))
