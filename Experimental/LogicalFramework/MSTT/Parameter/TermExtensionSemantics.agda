open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open TmExt
open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()

open ModeTheory ℳ

private variable
  m : Mode


-- A SemTmConstructor refers to an MSTT context and not a semantic
-- context. This has the advantage that it corresponds to the
-- arguments of the contructor Tm.ext.
SemTmConstructor : List (TmArgInfo m) → Ctx m → Ty m → Set
SemTmConstructor []                   Γ T = SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
SemTmConstructor (arginfo ∷ arginfos) Γ T =
  SemTm ⟦ Γ ++tel tmarg-tel arginfo ⟧ctx ⟦ tmarg-ty arginfo ⟧ty → SemTmConstructor arginfos Γ T

record TmExtSem (𝓉 : TmExt) : Set where
  no-eta-equality
  field
    ⟦_⟧tm-code : ∀ {m} → (c : TmExtCode 𝓉 m) → {Γ : Ctx m} → SemTmConstructor (tm-code-arginfos 𝓉 c) Γ (tm-code-ty 𝓉 c)
