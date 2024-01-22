--------------------------------------------------
-- Definition of the mode theory for parametricity
--------------------------------------------------

module Applications.Parametricity.MSTT.ModeTheory where

open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M hiding (★; ⋀)
open import Model.CwF-Structure as M
open import Model.DRA as DRA hiding (𝟙; id-cell)
open import Applications.Parametricity.Model as M hiding (forget-left; forget-right)

open import MSTT.TCMonad
open import MSTT.Parameter.ModeTheory


--------------------------------------------------
-- Expressions representing modes and modalities
-- We will not use 2-cells in this application, so only the trivial one is present.

data ModeExpr : Set where
  ★ ⋀ : ModeExpr

private
  variable
    m m' m'' : ModeExpr

data ModalityExpr : ModeExpr → ModeExpr → Set where
  𝟙 : ModalityExpr m m
  forget-left forget-right : ModalityExpr ⋀ ★

_ⓜ_ : ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
𝟙 ⓜ ρ = ρ
forget-left ⓜ 𝟙 = forget-left
forget-right ⓜ 𝟙 = forget-right

data TwoCellExpr : Set where
  id-cell : TwoCellExpr


--------------------------------------------------
-- Printing mode and modality expressions (mostly for type errors)

show-mode : ModeExpr → String
show-mode ★ = "★"
show-mode ⋀ = "⋀"

show-modality : ModalityExpr m m' → String
show-modality 𝟙 = "𝟙"
show-modality forget-left = "forget-left"
show-modality forget-right = "forget-right"


--------------------------------------------------
-- Interpretation of modes and modalities in a presheaf model

⟦_⟧mode : ModeExpr → BaseCategory
⟦ ★ ⟧mode = M.★
⟦ ⋀ ⟧mode = M.⋀

⟦_⟧modality : ModalityExpr m m' → DRA ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = DRA.𝟙
⟦ forget-left ⟧modality = M.forget-left
⟦ forget-right ⟧modality = M.forget-right

ⓜ-interpretation : (μ : ModalityExpr m' m'') (ρ : ModalityExpr m m') →
                   ⟦ μ ⓜ ρ ⟧modality ≅ᵈ ⟦ μ ⟧modality ⓓ ⟦ ρ ⟧modality
ⓜ-interpretation 𝟙 ρ = symᵈ (𝟙-unitˡ ⟦ ρ ⟧modality)
ⓜ-interpretation forget-left 𝟙 = symᵈ (𝟙-unitʳ M.forget-left)
ⓜ-interpretation forget-right 𝟙 = symᵈ (𝟙-unitʳ M.forget-right)


--------------------------------------------------
-- Equivalence of modes and modalities

_≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)
★ ≟mode ★ = return refl
⋀ ≟mode ⋀ = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
𝟙 ≟modality 𝟙 = return refl
forget-left ≟modality forget-left = return refl
forget-right ≟modality forget-right = return refl
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)

-- There are no interesting equivalences of modalities, we just check whether they are identical.
_≃ᵐ?_ : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵈ ⟦ ρ ⟧modality)
μ ≃ᵐ? ρ = do
  refl ← μ ≟modality ρ
  return reflᵈ


--------------------------------------------------
-- Interpretation of two-cells in a presheaf model

⟦_∈_⇒_⟧two-cell : TwoCellExpr → ∀ {m m'} (μ ρ : ModalityExpr m m') → TCM (TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality)
⟦ id-cell ∈ μ ⇒ ρ ⟧two-cell = do
  μ=ρ ← μ ≃ᵐ? ρ
  return (from μ=ρ)


--------------------------------------------------
-- The final definition of the mode theory

par-mode-theory : ModeTheory
ModeTheory.ModeExpr par-mode-theory = ModeExpr
ModeTheory.show-mode par-mode-theory = show-mode
ModeTheory.⟦_⟧mode par-mode-theory = ⟦_⟧mode
ModeTheory._≟mode_ par-mode-theory = _≟mode_
ModeTheory.ModalityExpr par-mode-theory = ModalityExpr
ModeTheory.𝟙 par-mode-theory = 𝟙
ModeTheory._ⓜ_ par-mode-theory = _ⓜ_
ModeTheory.show-modality par-mode-theory = show-modality
ModeTheory.⟦_⟧modality par-mode-theory = ⟦_⟧modality
ModeTheory.𝟙-interpretation par-mode-theory = reflᵈ
ModeTheory.ⓜ-interpretation par-mode-theory = ⓜ-interpretation
ModeTheory._≃ᵐ?_ par-mode-theory = _≃ᵐ?_
ModeTheory.TwoCellExpr par-mode-theory = TwoCellExpr
ModeTheory.id-cell par-mode-theory = id-cell
ModeTheory.⟦_∈_⇒_⟧two-cell par-mode-theory = ⟦_∈_⇒_⟧two-cell
