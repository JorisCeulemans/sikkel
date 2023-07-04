open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Data.String

module Experimental.LogicalFramework.MSTT.BasicPrograms
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯 String)
  where

open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ 𝒯 𝓉

private variable
  m n : Mode
  μ ρ : Modality m n
  Γ : Ctx m
  T S : Ty m


-- Every 2-cell gives rise to a coercion function
coe[_]_ : TwoCell μ ρ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
coe[_]_ {μ = μ} {ρ = ρ} α t = let' mod⟨ μ ⟩ "dummy" ← t in' (mod⟨ ρ ⟩ var "dummy" α)

-- Operations witnessing functoriality of modalities (up to isomorphism)
triv : Tm Γ T → Tm Γ ⟨ 𝟙 ∣ T ⟩
triv t = mod⟨ 𝟙 ⟩ lock𝟙-tm t

triv⁻¹ : Tm Γ ⟨ 𝟙 ∣ T ⟩ → Tm Γ T
triv⁻¹ t = let' mod⟨ 𝟙 ⟩ "dummy" ← t in' svar "dummy"

comp : Tm Γ ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩ → Tm Γ ⟨ μ ⓜ ρ ∣ T ⟩
comp {μ = μ} {ρ = ρ} t =
  let' mod⟨ μ ⟩ "dummy x" ← t in'
  let⟨ μ ⟩ mod⟨ ρ ⟩ "dummy y" ← svar "dummy x" in'
  (mod⟨ μ ⓜ ρ ⟩ svar "dummy y")

comp⁻¹ : Tm Γ ⟨ μ ⓜ ρ ∣ T ⟩ → Tm Γ ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩
comp⁻¹ {μ = μ} {ρ = ρ} t =
  let' mod⟨ μ ⓜ ρ ⟩ "dummy" ← t in'
  (mod⟨ μ ⟩ (mod⟨ ρ ⟩ svar "dummy"))

-- Applicative operator for modalities (every modality satisfies the K axiom).
infixl 50 _⊛_
_⊛_ : Tm Γ ⟨ μ ∣ T ⇛ S ⟩ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
_⊛_ {μ = μ} f t =
  let' mod⟨ μ ⟩ "dummy f" ← f in'
  let' mod⟨ μ ⟩ "dummy t" ← t [ π ]tm in'
  (mod⟨ μ ⟩ (svar "dummy f" ∙¹ svar "dummy t"))
