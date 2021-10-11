--------------------------------------------------
-- Type of the final result after type inference/interpretation
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)

module MSTT.TypeChecker.ResultType (mt : ModeTheory) (ty-ext : TyExt mt) where

open import Model.CwF-Structure

import MSTT.Syntax.Type
open MSTT.Syntax.Type mt ty-ext
open import MSTT.Syntax.Context mt ty-ext
open import MSTT.InterpretTypes mt ty-ext

open ModeTheory mt


-- The sound type checker will accept a term and a context and will then,
--   if successful, produce the type of that term and an interpretation of that
--   term in a presheaf model.
infix 1 _,_
record InferInterpretResult {m : ModeExpr} (Γ : CtxExpr m) : Set where
  constructor _,_
  field
    type : TyExpr m
    interpretation : Tm ⟦ Γ ⟧ctx ⟦ type ⟧ty
