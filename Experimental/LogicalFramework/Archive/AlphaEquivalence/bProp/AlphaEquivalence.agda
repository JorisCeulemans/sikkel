--------------------------------------------------
-- Definition of α-equivalence of bProps via a translation to nameless bProps
--------------------------------------------------

open import Data.String
open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension

module Experimental.LogicalFramework.bProp.AlphaEquivalence
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 String 𝓉)
  where

open import Data.List
open import Data.Product using (_,_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.bProp.AlphaEquivalence.bPropExtension 𝒫
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉
import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ 𝒯 (erase-names-tmext 𝓉) as NMLS-MSTT
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯

open import Experimental.LogicalFramework.bProp.Named 𝒫 𝒷
import Experimental.LogicalFramework.bProp.Nameless 𝒫 (erase-names-bpext 𝒷) as NMLS

private variable
  m : Mode
  Γ : Ctx m


erase-names-bprop : bProp Γ → NMLS.bProp (erase-names-ctx Γ)
erase-names-ext-bpargs : ∀ {arginfos} {Γ : Ctx m} → ExtBPArgs arginfos Γ →
                         NMLS.ExtBPArgs (map erase-names-arg-info arginfos) (erase-names-ctx Γ)

erase-names-bprop ⊤ᵇ = NMLS.⊤ᵇ
erase-names-bprop ⊥ᵇ = NMLS.⊥ᵇ
erase-names-bprop (t1 ≡ᵇ t2) = erase-names-tm t1 NMLS.≡ᵇ erase-names-tm t2
erase-names-bprop (⟨ μ ∣ φ ⟩⊃ ψ) = NMLS.⟨ μ ∣ erase-names-bprop φ ⟩⊃ erase-names-bprop ψ
erase-names-bprop (φ ∧ ψ) = erase-names-bprop φ NMLS.∧ erase-names-bprop ψ
erase-names-bprop (∀[ μ ∣ x ∈ T ] φ) = NMLS.∀[ μ ∣ _ ∈ T ] erase-names-bprop φ
erase-names-bprop ⟨ μ ∣ φ ⟩ = NMLS.⟨ μ ∣ erase-names-bprop φ ⟩
erase-names-bprop (ext c tmargs bpargs) = NMLS.ext c (erase-names-ext-tmargs tmargs) (erase-names-ext-bpargs bpargs)

erase-names-ext-bpargs {arginfos = []}           _                = tt
erase-names-ext-bpargs {arginfos = info ∷ _} {Γ} (bparg , bpargs) =
  subst (λ Δ → NMLS.bProp Δ) (erase-names-tel-++ Γ _) (erase-names-bprop bparg)
  ,
  erase-names-ext-bpargs bpargs


_≈αᵇ_ : (φ ψ : bProp Γ) → Set
φ ≈αᵇ ψ = erase-names-bprop φ ≡ erase-names-bprop ψ
