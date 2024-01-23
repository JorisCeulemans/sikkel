--------------------------------------------------
-- Specification of new term constructors for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.TermExtension where

open import Data.List
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M
open import Model.DRA as DRA hiding (⟨_∣_⟩)
open import Model.Type.Function as M hiding (_⇛_)
open import Applications.GuardedRecursion.Model.Modalities as M
  hiding (later; constantly; forever; ▻)
open import Applications.GuardedRecursion.Model.Streams.Guarded as M
  hiding (GStream; g-cons; g-head; g-tail)

open import Applications.GuardedRecursion.MSTT.ModeTheory
open import Applications.GuardedRecursion.MSTT.TypeExtension
open import Applications.GuardedRecursion.MSTT.Syntax.Type

open import MSTT.TCMonad
open import MSTT.Parameter.TermExtension GR-mode-theory GR-ty-ext
open import MSTT.Syntax.Context GR-mode-theory GR-ty-ext
open import MSTT.TypeChecker.ResultType GR-mode-theory GR-ty-ext
open import MSTT.Equivalence GR-mode-theory GR-ty-ext
open import MSTT.InterpretTypes GR-mode-theory GR-ty-ext

private variable
  m : ModeExpr
  margs : List ModeExpr


data GRTmCode : List ModeExpr → ModeExpr → Set where
  constantly-if-code : GRTmCode (ω ∷ ω ∷ ω ∷ []) ω
  löb-code : String → TyExpr ω → GRTmCode (ω ∷ []) ω
  g-cons-code g-head-code g-tail-code : TyExpr ★ → GRTmCode [] ω

infer-interpret-gr-code : GRTmCode margs m → InferInterpretExt margs m
infer-interpret-gr-code constantly-if-code = λ infer-c infer-t infer-f Γ → do
  C , ⟦c⟧ ← infer-c Γ
  modal-ty m μ B ← is-modal-ty C
  refl ← m ≟mode ★
  constantly=μ ← constantly ≃ᵐ? μ
  Bool'=B ← Bool' ≃ᵗʸ? B
  T , ⟦t⟧ ← infer-t Γ
  F , ⟦f⟧ ← infer-f Γ
  T=F ← T ≃ᵗʸ? F
  return (T , constantly-if' ι[ transᵗʸ (constantly-ty-cong Bool'=B) (eq-dra-ty-closed constantly=μ (⟦⟧ty-natural B)) ] ⟦c⟧
              then' ⟦t⟧ else' (ι[ T=F ] ⟦f⟧))
infer-interpret-gr-code (löb-code x T) = λ infer-t Γ → do
  S , ⟦t⟧ ← infer-t (Γ , later ∣ x ∈ T)
  T=S ← T ≃ᵗʸ? S
  return (T , löb' ⟦ T ⟧ty (ι[ transᵗʸ (closed-natural (⟦⟧ty-natural T) π) T=S ]
                            ι⁻¹[ closed-natural (⟦⟧ty-natural S) _ ]
                            ιc[ ,,-cong (▻-cong (closed-natural (⟦⟧ty-natural T) (from-earlier _))) ]' ⟦t⟧))
infer-interpret-gr-code (g-cons-code A) = λ Γ →
  return (⟨ constantly ∣ A ⟩ ⇛ ▻ (GStream A) ⇛ GStream A
         , ι⁻¹[ ⇛-cong reflᵗʸ (⇛-cong (▻-cong (closed-natural (⟦⟧ty-natural (GStream A)) _)) reflᵗʸ) ] M.g-cons)
infer-interpret-gr-code (g-head-code A) = λ Γ → return (GStream A ⇛ ⟨ constantly ∣ A ⟩ , M.g-head)
infer-interpret-gr-code (g-tail-code A) = λ Γ →
  return (GStream A ⇛ ▻ (GStream A)
         , (ι⁻¹[ ⇛-cong reflᵗʸ (▻-cong (closed-natural (⟦⟧ty-natural (GStream A)) (from-earlier _))) ] M.g-tail))

GR-tm-ext : TmExt
TmExt.TmExtCode GR-tm-ext = GRTmCode
TmExt.infer-interpret-code GR-tm-ext = infer-interpret-gr-code
