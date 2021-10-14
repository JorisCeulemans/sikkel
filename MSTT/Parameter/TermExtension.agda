--------------------------------------------------
-- An instance of MSTT can be extended with custom term constructors, and this
--   file provides the interface to do so. MSTT is parametrized by a record of
--   type TmExt, which specifies a universe of codes for the new term constructors
--   and the implementation of type inference for these constructors, as well as
--   their interpretation in a presheaf model.
--   Every code in the universe comes with a list of modes, representing the modes
--   of the constructor's arguments and a mode at which the resulting term will live.
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)

module MSTT.Parameter.TermExtension (mt : ModeTheory) (ty-ext : TyExt mt) where

open import Data.List

open import MSTT.TCMonad
open import MSTT.Syntax.Context mt ty-ext
open import MSTT.TypeChecker.ResultType mt ty-ext

open ModeTheory mt
open TyExt ty-ext

private variable
  m : ModeExpr
  margs : List ModeExpr


-- The type of the type inference/interpretation procedure for the new term constructors.
--   When inferring the type for a new constructor, we can infer the types of all of its
--   arguments in any context (living at the correct mode).
InferInterpretExt : List ModeExpr → ModeExpr → Set
InferInterpretExt []           m = (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
InferInterpretExt (m' ∷ margs) m = ((Γ : CtxExpr m') → TCM (InferInterpretResult Γ)) → InferInterpretExt margs m

record TmExt : Set₁ where
  field
    TmExtCode : List ModeExpr → ModeExpr → Set
    infer-interpret-code : TmExtCode margs m → InferInterpretExt margs m
