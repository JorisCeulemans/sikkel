module Experimental.LogicalFramework.Instances.GuardedRecursion.bPropExtension where

open import Data.Empty

open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension

open import Experimental.LogicalFramework.bProp.AlphaEquivalence.bPropExtension

open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics


guarded-bp-ext : bPropExt guarded-mt guarded-ty-ext _ guarded-tm-ext
bPropExt.bPropExtCode guarded-bp-ext _ = ⊥
bPropExt._≟bp-code_ guarded-bp-ext () ()
bPropExt.bp-code-tmarg-infos guarded-bp-ext ()
bPropExt.bp-code-bparg-infos guarded-bp-ext ()


guarded-bp-ext-sem : bPropExtSem guarded-mt guarded-ty-ext _ (erase-names-bpext guarded-mstt guarded-bp-ext)
bPropExtSem.⟦_⟧bp-code guarded-bp-ext-sem ()
