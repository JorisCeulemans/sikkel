--------------------------------------------------
-- Definition of the different expressions occurring
-- in the mode theory for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.ModeTheory.Expressions where

open import Data.String

open import Model.BaseCategory as M hiding (★; ω)
open import Model.CwF-Structure as M
open import Model.Modality as M hiding (𝟙; _ⓣ-vert_; _ⓣ-hor_; id-cell)
open import Applications.GuardedRecursion.Model.Modalities as M hiding
  (constantly; forever; later; 𝟙≤later; constantly∘forever≤𝟙)


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
  constantly : ModalityExpr ★ ω
  forever : ModalityExpr ω ★
  later : ModalityExpr ω ω

infixl 5 _ⓣ-hor_
infixl 6 _ⓣ-vert_
data TwoCellExpr : Set where
  id-cell : TwoCellExpr
  _ⓣ-vert_ : TwoCellExpr → TwoCellExpr → TwoCellExpr
    -- ^ Vertical composition of 2-cells, not used in examples.
  _ⓣ-hor_ : TwoCellExpr → TwoCellExpr → TwoCellExpr
    -- ^ Horizontal composition of 2-cells, not used in examples.
  𝟙≤later : TwoCellExpr
  constantly∘forever≤𝟙 : TwoCellExpr
  ann_∈_⇒_ : TwoCellExpr → ModalityExpr m m' → ModalityExpr m m' → TwoCellExpr
    -- ^ Used to annotate a 2-cell with its domain and codomain. E.g. useful in
    --   horizontal composition of the trivial 2-cell, which is not inferrable (see below).


--------------------------------------------------
-- Printing mode and modality expressions (mostly for type errors)

show-mode : ModeExpr → String
show-mode ★ = "★"
show-mode ω = "ω"

show-modality : ModalityExpr m m' → String
show-modality 𝟙 = "𝟙"
show-modality (μ ⓜ ρ) = show-modality μ ++ " ⓜ " ++ show-modality ρ
show-modality constantly = "constantly"
show-modality forever = "forever"
show-modality later = "later"


--------------------------------------------------
-- Interpretation of modes and modalities in the presheaf model

⟦_⟧mode : ModeExpr → BaseCategory
⟦ ★ ⟧mode = M.★
⟦ ω ⟧mode = M.ω

⟦_⟧modality : ModalityExpr m m' → DRA ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = M.𝟙
⟦ μ ⓜ ρ ⟧modality = ⟦ μ ⟧modality M.ⓓ ⟦ ρ ⟧modality
⟦ constantly ⟧modality = M.constantly
⟦ forever ⟧modality = M.forever
⟦ later ⟧modality = M.later
