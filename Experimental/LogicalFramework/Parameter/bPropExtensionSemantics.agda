open import Data.Unit
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯 ⊤)
  where

open import Data.List

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm)

open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 ⊤
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 ⊤
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 ⊤
open import Experimental.LogicalFramework.Parameter.bPropExtension ℳ 𝒯 ⊤ 𝓉
open bPropExt

open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Interpretation.Nameless ℳ 𝒯


SemPropConstructor : ∀ {m} → List (TmArgInfo m) → List (ArgInfo m) → Ctx m → Set₁
SemPropConstructor []                   []                   Γ = SemTy ⟦ Γ ⟧ctx-nmls
SemPropConstructor []                   (bp-info ∷ bp-infos) Γ =
  SemTy ⟦ Γ ++tel arg-tel bp-info ⟧ctx-nmls → SemPropConstructor [] bp-infos Γ
SemPropConstructor (tm-info ∷ tm-infos) bp-infos             Γ =
  SemTm ⟦ Γ ++tel tmarg-tel tm-info ⟧ctx-nmls ⟦ tmarg-ty tm-info ⟧ty → SemPropConstructor tm-infos bp-infos Γ

record bPropExtSem (𝒷 : bPropExt) : Set₁ where
  field
    ⟦_⟧bp-code : ∀ {m} → (c : bPropExtCode 𝒷 m) → {Γ : Ctx m} →
                 SemPropConstructor (bp-code-tmarg-infos 𝒷 c) (bp-code-bparg-infos 𝒷 c) Γ
