--------------------------------------------------
-- An instance of MSTT can be extended with custom type constructors, and this
--   file provides the interface to do so. MSTT is parametrized by a record of
--   type TyExt, which specifies among others a universe of codes for the new
--   type constructors, how these constructors will be interpreted in the presheaf
--   model, and proofs that this interpretation is a natural closed type.
--   Every code in the universe comes with a list of modes, representing the modes
--   of the constructor's arguments, and a mode at which the resulting type will live.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

module Experimental.LogicalFramework.MSTT.Parameter.TypeExtension (ℳ : ModeTheory) where

open import Data.List
open import Data.String hiding (show)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure

open import Experimental.LogicalFramework.Proof.CheckingMonad

open ModeTheory ℳ

private variable
  m : Mode
  margs : List Mode


TyExtShow : List Mode → Set
TyExtShow [] = String
TyExtShow (m ∷ margs) = String → TyExtShow margs

-- Every code is interpreted as a semantic type constructor working on closed types.
SemTyConstructor : List Mode → Mode → Set₁
SemTyConstructor []           m = ClosedTy ⟦ m ⟧mode
SemTyConstructor (m' ∷ margs) m = ClosedTy ⟦ m' ⟧mode → SemTyConstructor margs m

SemTyConstructorNatural : SemTyConstructor margs m → Set₁
SemTyConstructorNatural {[]}        T = IsClosedNatural T
SemTyConstructorNatural {m ∷ margs} F = {S : ClosedTy ⟦ m ⟧mode} → IsClosedNatural S → SemTyConstructorNatural (F S)

record TyExt : Set₁ where
  field
    TyExtCode : List Mode → Mode → Set
    _≟ty-code_ : (c1 c2 : TyExtCode margs m) → PCM (c1 ≡ c2)
    show-ty-code : TyExtCode margs m → TyExtShow margs
    ⟦_⟧ty-code : TyExtCode margs m → SemTyConstructor margs m
    sem-ty-code-natural : (c : TyExtCode margs m) → SemTyConstructorNatural (⟦ c ⟧ty-code)
