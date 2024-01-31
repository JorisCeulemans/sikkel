--------------------------------------------------
-- Definition of α-equivalence of MSTT terms via a translation to nameless terms
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Data.String

module Experimental.LogicalFramework.MSTT.AlphaEquivalence
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯 String)
  where

open import Data.List
open import Data.Product using (_,_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.Context ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension ℳ 𝒯

open import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ 𝒯 𝓉
import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ 𝒯 (erase-names-tmext 𝓉) as NMLS

open ModeTheory ℳ

private variable
  m n : Mode
  μ κ : Modality m n
  Γ : Ctx m
  T : Ty m
  x : String


erase-names-var : Var x μ T κ Γ → NMLS.Var _ μ T κ (erase-names-ctx Γ)
erase-names-var vzero = NMLS.vzero
erase-names-var (vsuc v) = NMLS.vsuc (erase-names-var v)
erase-names-var (skip-lock ρ v) = NMLS.skip-lock ρ (erase-names-var v)

erase-names-tm : Tm Γ T → NMLS.Tm (erase-names-ctx Γ) T
erase-names-ext-tmargs : ∀ {arginfos} → ExtTmArgs arginfos Γ → NMLS.ExtTmArgs (map erase-names-tmarg-info arginfos) (erase-names-ctx Γ)

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
erase-names-tm (ext c args ty-eq) = NMLS.ext c (erase-names-ext-tmargs args) ty-eq

erase-names-ext-tmargs {arginfos = []}                 args         = tt
erase-names-ext-tmargs {arginfos = arginfo ∷ arginfos} (arg , args) =
  (subst (λ Γ → NMLS.Tm Γ (tmarg-ty arginfo)) (erase-names-tel-++ _ (tmarg-tel arginfo)) (erase-names-tm arg)) , (erase-names-ext-tmargs args)


infix 2 _≈α_
_≈α_ : (t s : Tm Γ T) → Set
t ≈α s = erase-names-tm t ≡ erase-names-tm s
