open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.Parameter.ArgInfo
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where


open import Data.List
open import Data.Product
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯

open ModeTheory ℳ


record ArgInfo (m : Mode) : Set where
  no-eta-equality
  constructor arg-info
  field
    {mode} : Mode
    arg-tel : NamelessTele m mode
open ArgInfo public hiding (mode)

ArgBoundNames : {m : Mode} → List (ArgInfo m) → Set
ArgBoundNames []                   = ⊤
ArgBoundNames (arginfo ∷ arginfos) = Names (arg-tel arginfo) × ArgBoundNames arginfos
