--------------------------------------------------
-- Check whether a 2-cell can have the given modalities as its (co)domain and
--   interpretation in the presheaf model if successful
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.ModeTheory.TwoCells where

open import Relation.Binary.PropositionalEquality

open import MSTT.TCMonad

open import Applications.GuardedRecursion.MSTT.ModeTheory.Expressions
open import Applications.GuardedRecursion.MSTT.ModeTheory.Equivalence

open import Model.CwF-Structure as M
open import Model.Modality as M hiding (𝟙; _ⓣ-vert_; _ⓣ-hor_)
open import Applications.GuardedRecursion.Model.Modalities as M hiding
  (constantly; forever; later; 𝟙≤later; constantly∘forever≤𝟙)

private variable
  m m' : ModeExpr


-- The algorithm used is bidirectional: the (co)domain of some 2-cells can be inferred,
--   and for some (e.g. the trivial 2-cell) it must be checked. We require inference
--   of both sides in a composition so that we do not have to guess the modality
--   in the middle or check that a modality is a composition.

record TwoCellInferResult : Set₁ where
  constructor infer-result
  field
    n n' : ModeExpr
    μ ρ : ModalityExpr n n'
    interpretation : TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality

check-two-cell : TwoCellExpr → ∀ {m m'} → (μ ρ : ModalityExpr m m') → TCM (TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality)
infer-two-cell : TwoCellExpr → TCM TwoCellInferResult

check-two-cell id-cell μ ρ = do
  μ=ρ ← μ ≃ᵐ? ρ
  return (≅ᵈ-to-2-cell μ=ρ)
check-two-cell α {m} {n} μ ρ = do
  infer-result m' n' μ' ρ' ⟦α⟧ ← infer-two-cell α
  refl ← m ≟mode m'
  refl ← n ≟mode n'
  μ=μ' ← μ ≃ᵐ? μ'
  ρ'=ρ ← ρ' ≃ᵐ? ρ
  return (≅ᵈ-to-2-cell ρ'=ρ M.ⓣ-vert ⟦α⟧ M.ⓣ-vert ≅ᵈ-to-2-cell μ=μ')

infer-two-cell id-cell = type-error "Cannot infer the domain and codomain of the trivial 2-cell"
infer-two-cell (α ⓣ-vert β) = do
  infer-result mα nα μα ρα ⟦α⟧ ← infer-two-cell α
  infer-result mβ nβ μβ ρβ ⟦β⟧ ← infer-two-cell β
  refl ← mα ≟mode mβ
  refl ← nα ≟mode nβ
  ρβ=μα ← ρβ ≃ᵐ? μα
  return (infer-result mα nα μβ ρα (⟦α⟧ M.ⓣ-vert ≅ᵈ-to-2-cell ρβ=μα M.ⓣ-vert ⟦β⟧))
infer-two-cell (α ⓣ-hor β) = do
  infer-result mα nα μα ρα ⟦α⟧ ← infer-two-cell α
  infer-result mβ nβ μβ ρβ ⟦β⟧ ← infer-two-cell β
  refl ← mα ≟mode nβ
  return (infer-result mβ nα (μα ⓜ μβ) (ρα ⓜ ρβ) (⟦α⟧ M.ⓣ-hor ⟦β⟧))
infer-two-cell 𝟙≤later = return (infer-result ω ω 𝟙 later M.𝟙≤later)
infer-two-cell constantly∘forever≤𝟙 = return (infer-result ω ω (constantly ⓜ forever) 𝟙 M.constantly∘forever≤𝟙)
infer-two-cell (ann α ∈ μ ⇒ ρ) = do
  ⟦α⟧ ← check-two-cell α μ ρ
  return (infer-result _ _ μ ρ ⟦α⟧)
