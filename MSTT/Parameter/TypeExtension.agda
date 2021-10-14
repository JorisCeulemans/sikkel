--------------------------------------------------
-- An instance of MSTT can be extended with custom type constructors, and this
--   file provides the interface to do so. MSTT is parametrized by a record of
--   type TyExt, which specifies among others a universe of codes for the new
--   type constructors, how these constructors will be interpreted in the presheaf
--   model, and proofs that this interpretation is a congruence.
--   Every code in the universe comes with a list of modes, representing the modes
--   of the constructor's arguments and a mode at which the resulting type will live.
--------------------------------------------------

open import MSTT.Parameter.ModeTheory

module MSTT.Parameter.TypeExtension (mt : ModeTheory) where

open import Data.List
open import Data.String hiding (show)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure

open import MSTT.TCMonad

open ModeTheory mt

private variable
  m : ModeExpr
  margs : List ModeExpr


TyExtShow : List ModeExpr → Set
TyExtShow [] = String
TyExtShow (m ∷ margs) = String → TyExtShow margs

-- Every code is interpreted as a semantic type constructor working on closed types.
TyConstructor : List ModeExpr → ModeExpr → Set₁
TyConstructor [] m = ClosedTy ⟦ m ⟧mode
TyConstructor (m' ∷ margs) m = ClosedTy ⟦ m' ⟧mode → TyConstructor margs m

TyConstructorNatural : TyConstructor margs m → Set₁
TyConstructorNatural {[]}        T = IsClosedNatural T
TyConstructorNatural {m ∷ margs} F = {S : ClosedTy ⟦ m ⟧mode} → IsClosedNatural S → TyConstructorNatural (F S)

-- Type expressing that two semantic type constructors are equivalent, i.e. that they
--   produce equivalent types for equivalent inputs.
TyConstructorEquiv : TyConstructor margs m → TyConstructor margs m → Set₁
TyConstructorEquiv {[]}        T S = ∀ {Γ} → T {Γ} ≅ᵗʸ S
TyConstructorEquiv {m ∷ margs} F G = {T S : ClosedTy ⟦ m ⟧mode} → (∀ {Γ} → T {Γ} ≅ᵗʸ S) → TyConstructorEquiv (F T) (G S)

-- Type expressing that a semantic type constructor is a congruence, i.e. that it
--   respects equivalence of types ≅ᵗʸ.
TyConstructorCong : TyConstructor margs m → Set₁
TyConstructorCong F = TyConstructorEquiv F F

record TyExt : Set₁ where
  field
    TyExtCode : List ModeExpr → ModeExpr → Set
    _≟code_ : (c1 c2 : TyExtCode margs m) → TCM (c1 ≡ c2)
    show-code : TyExtCode margs m → TyExtShow margs
    interpret-code : TyExtCode margs m → TyConstructor margs m
    interpret-code-natural : (c : TyExtCode margs m) → TyConstructorNatural (interpret-code c)
    interpret-code-cong : (c : TyExtCode margs m) → TyConstructorCong (interpret-code c)
