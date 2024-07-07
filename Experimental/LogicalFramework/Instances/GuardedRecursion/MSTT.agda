module Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT where

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter

import Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory as GMT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.Normalization

open GMT
  using (ω; later; constantly; forever; guarded-mt; ltrⓜcst; ltr; 𝟙≤ltr; ltrⓜcstⓜfrv; cstⓜfrv≤𝟙; cstⓜfrv≤ltr)
  public
open ModeTheory guarded-mt public

guarded-mstt : MSTT-Parameter
MSTT-Parameter.ℳ guarded-mstt = guarded-mt
MSTT-Parameter.𝒯 guarded-mstt = guarded-ty-ext
MSTT-Parameter.𝓉 guarded-mstt = guarded-tm-ext
MSTT-Parameter.⟦𝓉⟧ guarded-mstt = guarded-tm-ext-sem
MSTT-Parameter.𝓉-norm guarded-mstt = guarded-tm-ext-norm


open import Experimental.LogicalFramework.MSTT guarded-mstt public
open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT.Syntax public
