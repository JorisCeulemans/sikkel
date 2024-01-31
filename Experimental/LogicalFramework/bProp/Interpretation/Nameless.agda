--------------------------------------------------
-- Interpretation of nameless propositions in the presheaf model over the
--   trivial base category
--------------------------------------------------

open import Data.List
open import Data.Product
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics using (bPropExtSem)
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension

module Experimental.LogicalFramework.bProp.Interpretation.Nameless
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 ⊤ (erase-names-tmext _ _ 𝓉))
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 (erase-names-tmext _ _ 𝓉) 𝒷)
  where

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.DRA as DRA
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

open import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ 𝒯 (erase-names-tmext _ _ 𝓉)
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Interpretation.Nameless ℳ 𝒯 (erase-names-tmext _ _ 𝓉) ⟦𝓉⟧
open import Experimental.LogicalFramework.bProp.Nameless 𝒫 𝒷
open Experimental.LogicalFramework.Parameter.bPropExtensionSemantics ℳ 𝒯 (erase-names-tmext _ _ 𝓉) hiding (bPropExtSem)

open bPropExtSem ⟦𝒷⟧

private variable
  m : Mode
  Γ : Ctx m


⟦_⟧bprop-nmls : bProp Γ → SemTy ⟦ Γ ⟧ctx-nmls
apply-sem-bprop-constructor : ∀ {m tmarginfos bparginfos} {Γ : Ctx m} →
  SemPropConstructor tmarginfos bparginfos Γ →
  ExtTmArgs tmarginfos Γ →
  ExtBPArgs bparginfos Γ →
  SemTy ⟦ Γ ⟧ctx-nmls

⟦ ⊤ᵇ ⟧bprop-nmls = M.Unit'
⟦ ⊥ᵇ ⟧bprop-nmls = M.Empty'
⟦ t1 ≡ᵇ t2 ⟧bprop-nmls = M.Id ⟦ t1 ⟧tm-nmls ⟦ t2 ⟧tm-nmls
⟦ ⟨ μ ∣ φ ⟩⊃ ψ ⟧bprop-nmls = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop-nmls ⟩ M.⇛ ⟦ ψ ⟧bprop-nmls
⟦ φ ∧ ψ ⟧bprop-nmls = ⟦ φ ⟧bprop-nmls M.⊠ ⟦ ψ ⟧bprop-nmls
⟦ ∀[ μ ∣ _ ∈ T ] φ ⟧bprop-nmls = M.Pi ⟦ ⟨ μ ∣ T ⟩ ⟧ty ⟦ φ ⟧bprop-nmls
⟦ ⟨ μ ∣ φ ⟩ ⟧bprop-nmls = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop-nmls ⟩
⟦ ext c tmargs bpargs ⟧bprop-nmls = apply-sem-bprop-constructor ⟦ c ⟧bp-code tmargs bpargs

apply-sem-bprop-constructor {tmarginfos = []}    {bparginfos = []}    φ tmargs           bpargs           = φ
apply-sem-bprop-constructor {tmarginfos = []}    {bparginfos = _ ∷ _} F tmargs           (bparg , bpargs) =
  apply-sem-bprop-constructor (F ⟦ bparg ⟧bprop-nmls) tmargs bpargs
apply-sem-bprop-constructor {tmarginfos = _ ∷ _} {bparginfos = y}     F (tmarg , tmargs) bpargs           =
  apply-sem-bprop-constructor (F ⟦ tmarg ⟧tm-nmls) tmargs bpargs
