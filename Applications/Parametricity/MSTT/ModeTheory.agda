--------------------------------------------------
-- Definition of the mode theory for parametricity
--------------------------------------------------

module Applications.Parametricity.MSTT.ModeTheory where

open import Data.String

open import Model.BaseCategory as M hiding (★; ⋀)
open import Model.Modality as M hiding (𝟙; _ⓜ_)
open import Applications.Parametricity.Model as M hiding (forget-left; forget-right)


--------------------------------------------------
-- Expressions representing modes and modalities
-- We will not use 2-cells in this application.

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
-- Interpretation of modes and modalities in a presheaf model.

⟦_⟧mode : ModeExpr → BaseCategory
⟦ ★ ⟧mode = M.★
⟦ ⋀ ⟧mode = M.⋀

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = M.𝟙
⟦ forget-left ⟧modality = M.forget-left
⟦ forget-right ⟧modality = M.forget-right

ⓜ-interpretation : (μ : ModalityExpr m' m'') (ρ : ModalityExpr m m') →
                   ⟦ μ ⓜ ρ ⟧modality ≅ᵐ ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
ⓜ-interpretation 𝟙 ρ = ≅ᵐ-sym (𝟙-identityˡ ⟦ ρ ⟧modality)
ⓜ-interpretation forget-left 𝟙 = ≅ᵐ-sym (𝟙-identityʳ M.forget-left)
ⓜ-interpretation forget-right 𝟙 = ≅ᵐ-sym (𝟙-identityʳ M.forget-right)


--------------------------------------------------
-- Equivalence of modes and modalities.

-- See Applications.Parametricity.MSTT.Equality
