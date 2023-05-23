module Experimental.DependentTypes.Model.IdentityType.Modal where

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Modality
open import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm


id-mod-intro-cong : {C D : BaseCategory} (μ : Modality C D) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)}
                    {t t' : Tm (Γ ,lock⟨ μ ⟩) T} →
                    Tm (Γ ,lock⟨ μ ⟩) (Id t t') → Tm Γ (Id (mod-intro μ t) (mod-intro μ t'))
id-mod-intro-cong μ e = ≅ᵗᵐ-to-Id (mod-intro-cong μ (eq-reflect e))
