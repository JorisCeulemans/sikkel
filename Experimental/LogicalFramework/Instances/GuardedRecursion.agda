module Experimental.LogicalFramework.Instances.GuardedRecursion where

open import Data.Unit
open import Data.Product

open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.bPropExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.ProofExtension

open import Experimental.LogicalFramework.Parameter



open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT public

guarded-param : BiSikkelParameter
BiSikkelParameter.𝒫 guarded-param = guarded-mstt
BiSikkelParameter.𝒷 guarded-param = guarded-bp-ext
BiSikkelParameter.⟦𝒷⟧ guarded-param = guarded-bp-ext-sem
BiSikkelParameter.𝓅 guarded-param = guarded-pf-ext

open import Experimental.LogicalFramework guarded-param public


pattern tmlöb-β = ext tmlöb-β-code tt tt tt tt tt tt
pattern pflöb x p = ext (pflöb-code x) tt tt tt tt ((tt , tt) , tt) (p , tt)
