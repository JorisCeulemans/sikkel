module Experimental.LogicalFramework.Instances.UnaryParametricity.MSTT where

open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter

import Experimental.LogicalFramework.Instances.UnaryParametricity.ModeTheory as UPMT
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension

open UPMT
  using (↑; forget; Σ;  unary-param-mt; π-cell)
  public
open ModeTheory unary-param-mt public

unary-param-mstt : MSTT-Parameter
MSTT-Parameter.ℳ unary-param-mstt = unary-param-mt
MSTT-Parameter.𝒯 unary-param-mstt = unary-param-ty-ext
MSTT-Parameter.𝓉 unary-param-mstt = unary-param-tm-ext
MSTT-Parameter.⟦𝓉⟧ unary-param-mstt = unary-param-tm-ext-sem
MSTT-Parameter.𝓉-norm unary-param-mstt = unary-param-tm-ext-norm


open import Experimental.LogicalFramework.MSTT unary-param-mstt public


pattern EncBool = Ext BinaryBool-code tt
pattern enc-true = ext true-code tt tt refl
pattern enc-false = ext false-code tt tt refl
pattern ∧' = ext and-code tt tt refl
pattern ¬' = ext not-code tt tt refl
