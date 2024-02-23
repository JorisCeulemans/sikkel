--------------------------------------------------
-- Specification of new term constructors for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.TermExtension where

open import Data.List
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M
open import Model.DRA as DRA hiding (⟨_∣_⟩; _,lock⟨_⟩)
open import Model.Type.Function as M hiding (_⇛_)
open import Applications.GuardedRecursion.Model.Modalities as M
  hiding (later; constantly; forever; ▻)
open import Applications.GuardedRecursion.Model.Modalities.Later.Closed as M using (löb-cl)
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
  g-cons-code : GRTmCode (★ ∷ ω ∷ []) ω
  g-head-code g-tail-code : GRTmCode (ω ∷ []) ω


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
  return (T , löb-cl (⟦⟧ty-natural T) (M.ι[ T=S ] ⟦t⟧))
infer-interpret-gr-code g-cons-code = λ infer-h infer-t Γ → do
  A , ⟦h⟧ ← infer-h (Γ ,lock⟨ constantly ⟩)
  B , ⟦t⟧ ← infer-t (Γ ,lock⟨ later ⟩)
  StrA=B ← GStream A ≃ᵗʸ? B
  return (GStream A
         , M.g-cons (M.constantly-tm ⟦h⟧) (M.ι[ ▻-cong (transᵗʸ (closed-natural (⟦⟧ty-natural (GStream A)) _) StrA=B) ] M.next ⟦t⟧))
infer-interpret-gr-code g-head-code = λ infer-s Γ → do
  B , ⟦s⟧ ← infer-s Γ
  gstr-ty A ← is-gstr-ty B
  return (⟨ constantly ∣ A ⟩ , M.g-head ⟦s⟧)
infer-interpret-gr-code g-tail-code = λ infer-s Γ → do
  B , ⟦s⟧ ← infer-s Γ
  gstr-ty A ← is-gstr-ty B
  return (▻ (GStream A) , (M.ι⁻¹[ ▻-cong (closed-natural (⟦⟧ty-natural (GStream A)) _) ] M.g-tail ⟦s⟧))

GR-tm-ext : TmExt
TmExt.TmExtCode GR-tm-ext = GRTmCode
TmExt.infer-interpret-code GR-tm-ext = infer-interpret-gr-code
