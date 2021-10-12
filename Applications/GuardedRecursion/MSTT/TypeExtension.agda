--------------------------------------------------
-- Specification of new type constructors for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.TypeExtension where

open import Data.List hiding (_++_)
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Applications.GuardedRecursion.Model.Streams.Guarded as M hiding (GStream)
open import Applications.GuardedRecursion.MSTT.ModeTheory

open import MSTT.TCMonad
open import MSTT.Parameter.TypeExtension GR-mode-theory

private variable
  m : ModeExpr
  margs : List ModeExpr


data GRTyCode : List ModeExpr → ModeExpr → Set where
  GStream-code : GRTyCode (★ ∷ []) ω

_≟gr-code_ : (c1 c2 : GRTyCode margs m) → TCM (c1 ≡ c2)
GStream-code ≟gr-code GStream-code = return refl

show-gr-code : GRTyCode margs m → TyExtShow margs
show-gr-code GStream-code = λ x → "GStream " ++ x

interpret-gr-code : GRTyCode margs m → TyConstructor margs m
interpret-gr-code GStream-code = λ A → M.GStream A

interpret-gr-code-natural : (c : GRTyCode margs m) → TyConstructorNatural (interpret-gr-code c)
interpret-gr-code-natural GStream-code = λ A-natural → gstream-closed {{A-natural}}

interpret-gr-code-cong : (c : GRTyCode margs m) → TyConstructorCong (interpret-gr-code c)
interpret-gr-code-cong GStream-code = λ A=B → gstream-cong A=B

GR-ty-ext : TyExt
TyExt.TyExtCode GR-ty-ext = GRTyCode
TyExt._≟code_ GR-ty-ext = _≟gr-code_
TyExt.show-code GR-ty-ext = show-gr-code
TyExt.interpret-code GR-ty-ext = interpret-gr-code
TyExt.interpret-code-natural GR-ty-ext = interpret-gr-code-natural
TyExt.interpret-code-cong GR-ty-ext = interpret-gr-code-cong
