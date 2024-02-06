open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.Parameter.ArgInfo
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (Name : Set)
  where


open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 Name

open ModeTheory ℳ


record ArgInfo (m : Mode) : Set where
  constructor arg-info
  field
    {mode} : Mode
    arg-tel : Telescope m mode
open ArgInfo public hiding (mode)
