module Experimental.LogicalFramework.MSTT.Parameter where

open import Data.String

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionNormalization


record MSTT-Parameter : Set₁ where
  no-eta-equality
  field
    ℳ : ModeTheory
    𝒯 : TyExt ℳ
    𝓉 : TmExt ℳ 𝒯
    ⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉
    𝓉-norm : TmExtNormalization ℳ 𝒯 𝓉 ⟦𝓉⟧

  -- When opening an MSTT parameter, all names introduced by the mode theory should be in scope.
  -- The fields of the type extension part should be brought into scope explicitly (they are needed less outside the MSTT definitions).
  open ModeTheory ℳ public
