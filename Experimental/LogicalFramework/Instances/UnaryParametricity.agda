module Experimental.LogicalFramework.Instances.UnaryParametricity where

open import Data.Unit
open import Data.Product

open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.bPropExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.ProofExtension

open import Experimental.LogicalFramework.Parameter



open import Experimental.LogicalFramework.Instances.UnaryParametricity.MSTT public

unary-param-param : BiSikkelParameter
BiSikkelParameter.𝒫 unary-param-param = unary-param-mstt
BiSikkelParameter.𝒷 unary-param-param = unary-param-bp-ext
BiSikkelParameter.⟦𝒷⟧ unary-param-param = unary-param-bp-ext-sem
BiSikkelParameter.𝓅 unary-param-param = unary-param-pf-ext

open import Experimental.LogicalFramework unary-param-param public


pattern Pred A a = ext (bPred-code A) (tt , tt) (a , tt) tt tt
pattern param A = ext (param-code A) tt tt tt tt tt tt
pattern extent-from A B f p = ext (extent-from-code A B) (tt , tt) (f , tt) tt tt (tt , tt) (p , tt)
