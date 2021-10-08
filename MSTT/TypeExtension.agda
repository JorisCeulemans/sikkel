open import MSTT.ModeTheory

module MSTT.TypeExtension (mt : ModeTheory) where

open import Data.List
open import Data.String hiding (show)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure

open import MSTT.TCMonad

open ModeTheory mt

private variable
  m : ModeExpr
  margs : List ModeExpr


ShowTyExtType : List ModeExpr → Set
ShowTyExtType [] = String
ShowTyExtType (m ∷ margs) = String → ShowTyExtType margs

InterpretTyExtType : List ModeExpr → ModeExpr → Set₁
InterpretTyExtType [] m = ClosedTy ⟦ m ⟧mode
InterpretTyExtType (m' ∷ margs) m = ClosedTy ⟦ m' ⟧mode → InterpretTyExtType margs m

TyExtNaturalityType : InterpretTyExtType margs m → Set₁
TyExtNaturalityType {[]}        T = IsClosedNatural T
TyExtNaturalityType {m ∷ margs} F = {S : ClosedTy ⟦ m ⟧mode} → IsClosedNatural S → TyExtNaturalityType (F S)

TyExtEquivType : InterpretTyExtType margs m → InterpretTyExtType margs m → Set₁
TyExtEquivType {[]}        T S = ∀ {Γ} → T {Γ} ≅ᵗʸ S
TyExtEquivType {m ∷ margs} F G = {T S : ClosedTy ⟦ m ⟧mode} → (∀ {Γ} → T {Γ} ≅ᵗʸ S) → TyExtEquivType (F T) (G S)

TyExtCongType : InterpretTyExtType margs m → Set₁
TyExtCongType F = TyExtEquivType F F

record TyExt : Set₁ where
  field
    TyExtCode : List ModeExpr → ModeExpr → Set
    _≟code_ : (c1 c2 : TyExtCode margs m) → TCM (c1 ≡ c2)
    show-code : TyExtCode margs m → ShowTyExtType margs
    interpret-code : TyExtCode margs m → InterpretTyExtType margs m
    interpret-code-natural : (c : TyExtCode margs m) → TyExtNaturalityType (interpret-code c)
    interpret-code-cong : (c : TyExtCode margs m) → TyExtCongType (interpret-code c)
    
