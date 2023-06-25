--------------------------------------------------
-- Definition of α-equivalence of MSTT terms via a translation to nameless terms
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.AlphaEquivalence
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.String
open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ 𝒯
import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ 𝒯 as NMLS

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

erase-names-var : Var x μ T κ Γ → NMLS.Var _ μ T κ (erase-names-ctx Γ)
erase-names-var vzero = NMLS.vzero
erase-names-var (vsuc v) = NMLS.vsuc (erase-names-var v)
erase-names-var (skip-lock ρ v) = NMLS.skip-lock ρ (erase-names-var v)

erase-names-tm : Tm Γ T → NMLS.Tm (erase-names-ctx Γ) T
erase-names-tm (var' x {v} α) = NMLS.var' _ {erase-names-var v} α
erase-names-tm (mod⟨ μ ⟩ t) = NMLS.mod⟨ μ ⟩ erase-names-tm t
erase-names-tm (mod-elim ρ μ x t s) = NMLS.mod-elim ρ μ _ (erase-names-tm t) (erase-names-tm s)
erase-names-tm (lam[ μ ∣ x ∈ T ] t) = NMLS.lam[ μ ∣ _ ∈ T ] erase-names-tm t
erase-names-tm (f ∙ t) = (erase-names-tm f) NMLS.∙ (erase-names-tm t)
erase-names-tm zero = NMLS.zero
erase-names-tm (suc n) = NMLS.suc (erase-names-tm n)
erase-names-tm (nat-rec a f n) = NMLS.nat-rec (erase-names-tm a) (erase-names-tm f) (erase-names-tm n)
erase-names-tm true = NMLS.true
erase-names-tm false = NMLS.false
erase-names-tm (if b t f) = NMLS.if (erase-names-tm b) (erase-names-tm t) (erase-names-tm f)
erase-names-tm (pair t s) = NMLS.pair (erase-names-tm t) (erase-names-tm s)
erase-names-tm (fst p) = NMLS.fst (erase-names-tm p)
erase-names-tm (snd p) = NMLS.snd (erase-names-tm p)

infix 2 _≈α_
_≈α_ : (t s : Tm Γ T) → Set
t ≈α s = erase-names-tm t ≡ erase-names-tm s
