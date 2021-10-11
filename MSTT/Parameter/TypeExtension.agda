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

TyConstructor : List ModeExpr → ModeExpr → Set₁
TyConstructor [] m = ClosedTy ⟦ m ⟧mode
TyConstructor (m' ∷ margs) m = ClosedTy ⟦ m' ⟧mode → TyConstructor margs m

TyConstructorNatural : TyConstructor margs m → Set₁
TyConstructorNatural {[]}        T = IsClosedNatural T
TyConstructorNatural {m ∷ margs} F = {S : ClosedTy ⟦ m ⟧mode} → IsClosedNatural S → TyConstructorNatural (F S)

TyConstructorEquiv : TyConstructor margs m → TyConstructor margs m → Set₁
TyConstructorEquiv {[]}        T S = ∀ {Γ} → T {Γ} ≅ᵗʸ S
TyConstructorEquiv {m ∷ margs} F G = {T S : ClosedTy ⟦ m ⟧mode} → (∀ {Γ} → T {Γ} ≅ᵗʸ S) → TyConstructorEquiv (F T) (G S)

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
