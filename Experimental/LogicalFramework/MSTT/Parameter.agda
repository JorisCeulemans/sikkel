module Experimental.LogicalFramework.MSTT.Parameter where

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension


record MSTT-Parameter : Set₁ where
  field
    ℳ : ModeTheory
    𝒯 : TyExt ℳ

  -- When opening an MSTT parameter, all names introduced by the mode theory should be in scope.
  -- The fields of the type extension part should be brought into scope explicitly (they are needed less outside the MSTT definitions).
  open ModeTheory ℳ public
