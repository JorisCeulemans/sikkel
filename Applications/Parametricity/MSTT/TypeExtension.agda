--------------------------------------------------
-- Specification of new type constructors for parametricity
--------------------------------------------------

open import Applications.Parametricity.MSTT.TypeExtension.RelExtension

module Applications.Parametricity.MSTT.TypeExtension (rel-ext : RelExt) where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M
open import Applications.Parametricity.Model as M hiding (FromRel)

open import MSTT.TCMonad
open import Applications.Parametricity.MSTT.ModeTheory
open import MSTT.Parameter.TypeExtension par-mode-theory

open RelExt rel-ext

private variable
  m : ModeExpr
  margs : List ModeExpr


data ParTyCode : List ModeExpr → ModeExpr → Set where
  FromRel-code : RelCode → ParTyCode [] ⋀

_≟par-code_ : (c1 c2 : ParTyCode margs m) → TCM (c1 ≡ c2)
FromRel-code c1 ≟par-code FromRel-code c2 = do
  refl ← c1 ≟code c2
  return refl

show-par-code : ParTyCode margs m → TyExtShow margs
show-par-code (FromRel-code c) = show-code c

interpret-par-code : ParTyCode margs m → TyConstructor margs m
interpret-par-code (FromRel-code c) = M.FromRel (CodeLeft c) (CodeRight c) (CodeRelation c)

interpret-par-code-natural : (c : ParTyCode margs m) → TyConstructorNatural (interpret-par-code c)
interpret-par-code-natural (FromRel-code c) = fromrel-natural

interpret-par-code-cong : (c : ParTyCode margs m) → TyConstructorCong (interpret-par-code c)
interpret-par-code-cong (FromRel-code c) = reflᵗʸ

par-ty-ext : TyExt
TyExt.TyExtCode par-ty-ext = ParTyCode
TyExt._≟code_ par-ty-ext = _≟par-code_
TyExt.show-code par-ty-ext = show-par-code
TyExt.interpret-code par-ty-ext = interpret-par-code
TyExt.interpret-code-natural par-ty-ext = interpret-par-code-natural
TyExt.interpret-code-cong par-ty-ext = interpret-par-code-cong
