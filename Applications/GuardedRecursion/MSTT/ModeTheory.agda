--------------------------------------------------
-- Definition of the mode theory for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.ModeTheory where

open import Data.String

open import Model.BaseCategory as M hiding (★; ω)
open import Model.CwF-Structure as M hiding (_ⓣ-vert_; _ⓣ-hor_)
open import Model.Modality as M hiding (𝟙; _ⓜ_)
open import Applications.GuardedRecursion.Model.Modalities as M hiding
  (timeless; allnow; later; 𝟙≤later; timeless∘allnow≤𝟙)


--------------------------------------------------
-- Expressions representing modes, modalities and 2-cells

data ModeExpr : Set where
  ★ ω : ModeExpr

private
  variable
    m m' m'' : ModeExpr

infixl 5 _ⓜ_
data ModalityExpr : ModeExpr → ModeExpr → Set where
  𝟙 : ModalityExpr m m
  _ⓜ_ : ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
  timeless : ModalityExpr ★ ω
  allnow : ModalityExpr ω ★
  later : ModalityExpr ω ω

data TwoCellExpr : ModalityExpr m m' → ModalityExpr m m' → Set where
  id-cell : (μ : ModalityExpr m m') → TwoCellExpr μ μ
  _ⓣ-vert_ : {μ ρ κ : ModalityExpr m m'} → TwoCellExpr ρ κ → TwoCellExpr μ ρ → TwoCellExpr μ κ
    -- ^ Vertical composition of 2-cells, not used in examples.
  _ⓣ-hor_ : {μ μ' : ModalityExpr m' m''} {ρ ρ' : ModalityExpr m m'} →
            TwoCellExpr μ μ' → TwoCellExpr ρ ρ' → TwoCellExpr (μ ⓜ ρ) (μ' ⓜ ρ')
    -- ^ Horizontal composition of 2-cells, not used in examples.
  𝟙≤later : TwoCellExpr 𝟙 later
  timeless∘allnow≤𝟙 : TwoCellExpr (timeless ⓜ allnow) 𝟙


--------------------------------------------------
-- Printing mode and modality expressions (mostly for type errors)

show-mode : ModeExpr → String
show-mode ★ = "★"
show-mode ω = "ω"

show-modality : ModalityExpr m m' → String
show-modality 𝟙 = "𝟙"
show-modality (μ ⓜ ρ) = show-modality μ ++ " ⓜ " ++ show-modality ρ
show-modality timeless = "timeless"
show-modality allnow = "allnow"
show-modality later = "later"


--------------------------------------------------
-- Interpretation of modes, modalities and 2-cells in the presheaf model

⟦_⟧mode : ModeExpr → Category
⟦ ★ ⟧mode = M.★
⟦ ω ⟧mode = M.ω

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = M.𝟙
⟦ μ ⓜ ρ ⟧modality = ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
⟦ timeless ⟧modality = M.timeless
⟦ allnow ⟧modality = M.allnow
⟦ later ⟧modality = M.later

⟦_⟧two-cell : {μ ρ : ModalityExpr m m'} → TwoCellExpr μ ρ → TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality
⟦ id-cell _ ⟧two-cell = two-cell (id-ctx-transf _)
⟦ α ⓣ-vert β ⟧two-cell = two-cell (transf ⟦ β ⟧two-cell M.ⓣ-vert transf ⟦ α ⟧two-cell)
⟦ α ⓣ-hor β ⟧two-cell = two-cell (transf ⟦ β ⟧two-cell M.ⓣ-hor transf ⟦ α ⟧two-cell)
⟦ 𝟙≤later ⟧two-cell = M.𝟙≤later
⟦ timeless∘allnow≤𝟙 ⟧two-cell = M.timeless∘allnow≤𝟙


--------------------------------------------------
-- Equivalence of modes and modalities.

-- See Applications.GuardedRecursion.MSTT.Equality
