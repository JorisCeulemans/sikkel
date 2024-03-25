open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.Parameter.bPropExtension
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where


open import Data.List
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯

open ModeTheory ℳ

private variable
  m : Mode


record bPropExt : Set₁ where
  no-eta-equality
  field
    bPropExtCode : Mode → Set
      -- ^ The universe of codes, every code corresponds to a new proposition former.
    _≟bp-code_ : (c1 c2 : bPropExtCode m) → PCM (c1 ≡ c2)
      -- ^ We should be able to test codes for equality.
    bp-code-tmarg-infos : (c : bPropExtCode m) → List (TmArgInfo m)
      -- ^ A proposition may depend on one or more terms (i.e. it may
      --   be a predicate). We keep a list of their types and
      --   telescopes that change the context those terms live in.
    bp-code-bparg-infos : (c : bPropExtCode m) → List (ArgInfo m)
      -- ^ A proposition former can take other propositions as
      --   arguments. Those can live at different modes and in a
      --   modified context, which is stored in values of the type
      --   ArgInfo.
