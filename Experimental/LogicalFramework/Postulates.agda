-- This module lists all axioms that are currently postulated.
-- They should eventually be proved.

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.Postulates
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Data.String using (String)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M

open ModeTheory ℳ
open ModeTheoryInterpretation ⟦ℳ⟧

open import Experimental.LogicalFramework.MSTT ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.Formula ℳ ⟦ℳ⟧

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n


postulate
  tm-sub-sound : (t : Tm Δ T) (σ : Sub Γ Δ) → ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧sub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
  frm-sub-sound : (φ : Formula Δ) (σ : Sub Γ Δ) → ⟦ φ ⟧frm M.[ ⟦ σ ⟧sub ] M.≅ᵗʸ ⟦ φ [ σ ]frm ⟧frm

  unlock𝟙-frm-sound : (φ : Formula (Γ ,lock⟨ 𝟙 ⟩)) → ⟦ unlock𝟙-frm φ ⟧frm M.≅ᵗʸ ⟦ φ ⟧frm
  unfuselocks-frm-sound : {μ : Modality n o} {ρ : Modality m n} (φ : Formula (Γ ,lock⟨ μ ⓜ ρ ⟩)) →
                          ⟦ unfuselocks-frm {μ = μ} φ ⟧frm M.≅ᵗʸ ⟦ φ ⟧frm M.[ M.to (M.eq-lock (⟦ⓜ⟧-sound μ ρ) _) ]

  key-sub-sound : {μ ρ : Modality m n} (α : TwoCell μ ρ) {Γ : Ctx n} →
                  M.key-subst ⟦ α ⟧two-cell M.≅ˢ ⟦ key-sub {Γ = Γ} (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ μ ⟩) α ⟧sub
  sub-lock-sound : (σ : Sub Γ Δ) (μ : Modality m n) → ⟦ σ ,slock⟨ μ ⟩ ⟧sub M.≅ˢ M.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧sub
  sub-π-sound : {Γ : Ctx m} {x : String} {μ : Modality n m} {T : Ty n} → ⟦ π {Γ = Γ} {μ = μ} {x} {T} ⟧sub M.≅ˢ M.π
