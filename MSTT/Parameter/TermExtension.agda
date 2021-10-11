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


InferInterpretExt : List ModeExpr → ModeExpr → Set
InferInterpretExt []           m = (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
InferInterpretExt (m' ∷ margs) m = ((Γ : CtxExpr m') → TCM (InferInterpretResult Γ)) → InferInterpretExt margs m

record TmExt : Set₁ where
  field
    TmExtCode : List ModeExpr → ModeExpr → Set
    infer-interpret-code : TmExtCode margs m → InferInterpretExt margs m
