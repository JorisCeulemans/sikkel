module Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT where

open import Data.Product using (_,_)
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter

import Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory as GMT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension


open GMT using (★; ω; later; constantly; forever; guarded-mt) public
open ModeTheory guarded-mt public

guarded-mstt : MSTT-Parameter
MSTT-Parameter.ℳ guarded-mstt = guarded-mt
MSTT-Parameter.𝒯 guarded-mstt = guarded-ty-ext
MSTT-Parameter.𝓉 guarded-mstt = guarded-tm-ext
MSTT-Parameter.⟦𝓉⟧ guarded-mstt = guarded-tm-ext-sem


open import Experimental.LogicalFramework.MSTT guarded-mstt public

pattern GStream A = Ext GStream-code (A , tt)
pattern löb[later∣_∈_]_ x A t = ext (löb-code x A) (t , tt) refl
pattern g-cons {A} h t = ext (g-cons-code A) (h , t , tt) refl
pattern g-head {A} s = ext (g-head-code A) (s , tt) refl
pattern g-tail {A} s = ext (g-tail-code A) (s , tt) refl
