module Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics where

open import Model.BaseCategory as M using (BaseCategory)
open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.Modality as M using (_≅ᵐ_)

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory


record MTSemBasis (ℳ : ModeTheory) : Set₁ where
  open ModeTheory ℳ

  field
    ⟦_⟧mode : Mode → BaseCategory
    ⟦_⟧non-triv-mod : ∀ {m n} → NonTrivModality m n → M.Modality ⟦ m ⟧mode ⟦ n ⟧mode

  ⟦_⟧mod : ∀ {m n} → Modality m n → M.Modality ⟦ m ⟧mode ⟦ n ⟧mode
  ⟦ 𝟙 ⟧mod = M.𝟙
  ⟦ ‵ μ ⟧mod = ⟦ μ ⟧non-triv-mod

  ⟦𝟙⟧-sound : ∀ {m} → ⟦ 𝟙 {m} ⟧mod ≅ᵐ M.𝟙
  ⟦𝟙⟧-sound = M.reflᵐ


record MTSemCompletion (ℳ : ModeTheory) (mtsb : MTSemBasis ℳ) : Set₁ where
  open ModeTheory ℳ
  open MTSemBasis mtsb

  field
    ⟦ⓜ⟧-non-triv-sound : ∀ {m n o} (μ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵐ ⟦ μ ⟧non-triv-mod M.ⓜ ⟦ κ ⟧non-triv-mod
    ⟦_⟧two-cell : ∀ {m n} {μ κ : Modality m n} → TwoCell μ κ → M.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod

  ⟦ⓜ⟧-sound : ∀ {m n o} (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵐ ⟦ μ ⟧mod M.ⓜ ⟦ κ ⟧mod
  ⟦ⓜ⟧-sound 𝟙     κ     = M.symᵐ (M.𝟙-unitˡ _)
  ⟦ⓜ⟧-sound (‵ μ) 𝟙     = M.symᵐ (M.𝟙-unitʳ _)
  ⟦ⓜ⟧-sound (‵ μ) (‵ κ) = ⟦ⓜ⟧-non-triv-sound μ κ
    

record ModeTheorySemantics (ℳ : ModeTheory) : Set₁ where
  field
    mtsb : MTSemBasis ℳ
    mtsc : MTSemCompletion ℳ mtsb

  open MTSemBasis mtsb public
  open MTSemCompletion mtsc public
