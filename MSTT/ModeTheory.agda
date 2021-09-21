module MSTT.ModeTheory where

open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.Modality as M hiding (𝟙; _ⓜ_)

open import MSTT.TCMonad


record ModeTheory : Set₁ where
  field
    ModeExpr : Set
    show-mode : ModeExpr → String
    ⟦_⟧mode : ModeExpr → Category
    _≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)

    ModalityExpr : ModeExpr → ModeExpr → Set
    𝟙 : ∀ {m} → ModalityExpr m m
    _ⓜ_ : ∀ {m m' m''} → ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
    show-modality : ∀ {m m'} → ModalityExpr m m' → String
    ⟦_⟧modality : ∀ {m m'} → ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
    𝟙-interpretation : ∀ {m} → ⟦ 𝟙 {m} ⟧modality ≅ᵐ M.𝟙
    ⓜ-interpretation : ∀ {m m' m''} (μ : ModalityExpr m' m'') (ρ : ModalityExpr m m') →
                       ⟦ μ ⓜ ρ ⟧modality ≅ᵐ ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
    ⟦_⟧≅mod?⟦_⟧ : ∀ {m m'} (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality)

    TwoCellExpr : ∀ {m m'} → ModalityExpr m m' → ModalityExpr m m' → Set
    ⟦_⟧two-cell : ∀ {m m'} {μ ρ : ModalityExpr m m'} → TwoCellExpr μ ρ → TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality
