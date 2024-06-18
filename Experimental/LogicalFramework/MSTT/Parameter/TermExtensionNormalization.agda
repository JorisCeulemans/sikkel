open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics

module Experimental.LogicalFramework.MSTT.Parameter.TermExtensionNormalization
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.Maybe

open Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
  renaming (TmArgInfo to DependencyInfo; tmarg-tel to dep-tel; tmarg-ty to dep-ty)
  hiding (TmExt)
open TmExt 𝓉
open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Terms ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Normalization.ResultType ℳ 𝒯 𝓉 ⟦𝓉⟧

open ModeTheory ℳ

private variable
  m n : Mode
  Γ : Ctx m


record TmExtNormalization : Set where
  field
    normalize-tm-code : ({n : Mode} {Γ : Ctx n} {T : Ty n} (t : Tm Γ T) → Maybe (NormalizeResult t)) →
                        {m : Mode} (c : TmExtCode m) {Γ : Ctx m} (tmargs : ExtTmArgs (tm-code-arginfos c) Γ) →
                        Maybe (NormalizeResult (ext c tmargs refl))
