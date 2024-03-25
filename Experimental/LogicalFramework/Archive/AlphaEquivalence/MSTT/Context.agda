open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.AlphaEquivalence.Context
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.String
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 String
import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 ⊤ as NMLS

private variable
  m n : Mode
  μ κ : Modality m n
  Γ : Ctx m
  T : Ty m
  x : String


erase-names-ctx : Ctx m → NMLS.Ctx m
erase-names-ctx ◇ = NMLS.◇
erase-names-ctx (Γ ,, μ ∣ x ∈ T) = erase-names-ctx Γ NMLS.,, μ ∣ _ ∈ T
erase-names-ctx (Γ ,lock⟨ μ ⟩) = erase-names-ctx Γ NMLS.,lock⟨ μ ⟩

erase-names-tel : Telescope m n → NMLS.Telescope m n
erase-names-tel ◇ = NMLS.◇
erase-names-tel (Θ ,, μ ∣ x ∈ T) = erase-names-tel Θ NMLS.,, μ ∣ _ ∈ T
erase-names-tel (Θ ,lock⟨ μ ⟩) = erase-names-tel Θ NMLS.,lock⟨ μ ⟩

erase-names-tel-++ : (Γ : Ctx m) (Θ : Telescope m n) →
  erase-names-ctx (Γ ++tel Θ) ≡ erase-names-ctx Γ NMLS.++tel erase-names-tel Θ
erase-names-tel-++ Γ ◇ = refl
erase-names-tel-++ Γ (Θ ,, μ ∣ x ∈ T) = cong (λ Δ → Δ NMLS.,, μ ∣ _ ∈ T) (erase-names-tel-++ Γ Θ)
erase-names-tel-++ Γ (Θ ,lock⟨ μ ⟩) = cong (λ Δ → Δ NMLS.,lock⟨ μ ⟩) (erase-names-tel-++ Γ Θ)
