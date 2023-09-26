module Experimental.DependentTypes.Model.IdentityType.Modal where

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA
open import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm


id-dra-intro-cong : {C D : BaseCategory} (μ : DRA C D) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)}
                    {t t' : Tm (Γ ,lock⟨ μ ⟩) T} →
                    Tm (Γ ,lock⟨ μ ⟩) (Id t t') → Tm Γ (Id (dra-intro μ t) (dra-intro μ t'))
id-dra-intro-cong μ e = ≅ᵗᵐ-to-Id (dra-intro-cong μ (eq-reflect e))
