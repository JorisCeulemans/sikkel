module Experimental.LogicalFramework.MSTT.BasicPrograms where

open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Named

private variable
  m n : Mode
  μ ρ : Modality m n
  Γ : Ctx m
  T S : Ty m


coe[_]_ : TwoCell μ ρ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
coe[_]_ {μ = μ} {ρ = ρ} α t = let' mod⟨ μ ⟩ "dummy" ← t in' (mod⟨ ρ ⟩ var "dummy" (subst (TwoCell μ) (sym mod-unitˡ) α))

triv : Tm Γ T → Tm Γ ⟨ 𝟙 ∣ T ⟩
triv t = mod⟨ 𝟙 ⟩ lock𝟙-tm t

triv⁻¹ : Tm Γ ⟨ 𝟙 ∣ T ⟩ → Tm Γ T
triv⁻¹ t = let' mod⟨ 𝟙 ⟩ "dummy" ← t in' svar "dummy"

comp : Tm Γ ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩ → Tm Γ ⟨ μ ⓜ ρ ∣ T ⟩
comp {μ = μ} {ρ = ρ} t =
  let' mod⟨ μ ⟩ "dummy x" ← t in'
  let⟨ μ ⟩ mod⟨ ρ ⟩ "dummy y" ← var "dummy x" (subst (TwoCell μ) (sym mod-unitˡ) id-cell) in'
  (mod⟨ μ ⓜ ρ ⟩ var "dummy y" (subst (TwoCell _) (sym mod-unitˡ) id-cell))

comp⁻¹ : Tm Γ ⟨ μ ⓜ ρ ∣ T ⟩ → Tm Γ ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩
comp⁻¹ {μ = μ} {ρ = ρ} t =
  let' mod⟨ μ ⓜ ρ ⟩ "dummy" ← t in'
  (mod⟨ μ ⟩ (mod⟨ ρ ⟩ var "dummy" (subst (TwoCell _) (cong (_ⓜ ρ) (sym mod-unitˡ)) id-cell)))

_⊛_ : Tm Γ ⟨ μ ∣ T ⇛ S ⟩ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
_⊛_ {μ = μ} f t =
  let' mod⟨ μ ⟩ "dummy f" ← f in'
  let' mod⟨ μ ⟩ "dummy t" ← t [ π ]tm in'
  (mod⟨ μ ⟩ (var "dummy f" (subst (TwoCell μ) (sym mod-unitˡ) id-cell) ∙ var "dummy t" (subst (TwoCell μ) (sym mod-unitˡ) id-cell)))
