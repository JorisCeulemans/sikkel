--------------------------------------------------
-- Specification of new term constructors for parametricity
--------------------------------------------------

open import Applications.Parametricity.MSTT.TypeExtension.RelExtension

module Applications.Parametricity.MSTT.TermExtension (rel-ext : RelExt) where

open import Data.List

open import Model.CwF-Structure as M
import Model.Type.Function as M
open import Applications.Parametricity.Model as M using (_⟨→⟩_)

open import Applications.Parametricity.MSTT.ModeTheory
open import Applications.Parametricity.MSTT.TypeExtension rel-ext
open import MSTT.Parameter.TermExtension par-mode-theory par-ty-ext

open import MSTT.TCMonad
open import MSTT.TypeChecker.ResultType par-mode-theory par-ty-ext
open import Applications.Parametricity.MSTT.Syntax.Type
open import MSTT.InterpretTypes par-mode-theory par-ty-ext

open RelExt rel-ext

private variable
  m : ModeExpr
  margs : List ModeExpr


data ParTmCode : List ModeExpr → ModeExpr → Set where
  from-rel-code : (c : RelCode) (a : CodeLeft c) (b : CodeRight c) →
                  CodeRelation c a b → ParTmCode [] ⋀
  from-rel1-code : (c1 c2 : RelCode)
                   (f : CodeLeft  c1 → CodeLeft  c2)
                   (g : CodeRight c1 → CodeRight c2) →
                   (CodeRelation c1 ⟨→⟩ CodeRelation c2) f g →
                   ParTmCode [] ⋀
  from-rel2-code : (c1 c2 c3 : RelCode)
                   (f : CodeLeft  c1 → CodeLeft  c2 → CodeLeft  c3)
                   (g : CodeRight c1 → CodeRight c2 → CodeRight c3) →
                   (CodeRelation c1 ⟨→⟩ CodeRelation c2 ⟨→⟩ CodeRelation c3) f g →
                   ParTmCode [] ⋀

infer-interpret-par-code : ParTmCode margs m → InferInterpretExt margs m
infer-interpret-par-code (from-rel-code c a b r) = λ Γ → return (FromRel c , M.from-rel a b r)
infer-interpret-par-code (from-rel1-code c1 c2 f g r) = λ Γ →
  return (FromRel c1 ⇛ FromRel c2 , M.lam _ (ι[ closed-natural {{⟦⟧ty-natural (FromRel c2)}} π ] M.from-rel1 f g r))
infer-interpret-par-code (from-rel2-code c1 c2 c3 f g r) = λ Γ → return
  (FromRel c1 ⇛ FromRel c2 ⇛ FromRel c3
  , M.lam _ (ι[ closed-natural {{⟦⟧ty-natural (FromRel c2 ⇛ FromRel c3)}} π ]
      M.lam _ (ι[ closed-natural {{⟦⟧ty-natural (FromRel c3)}} π ]
        M.from-rel2 f g r)))


par-tm-ext : TmExt
TmExt.TmExtCode par-tm-ext = ParTmCode
TmExt.infer-interpret-code par-tm-ext = infer-interpret-par-code
