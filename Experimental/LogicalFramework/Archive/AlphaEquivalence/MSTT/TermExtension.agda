open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List
open import Data.String
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 String
import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 ⊤ as NMLS

open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.Context ℳ 𝒯

open ModeTheory ℳ

private variable
  m : Mode


erase-names-tmarg-info : TmArgInfo m → NMLS.TmArgInfo m
erase-names-tmarg-info arginfo = NMLS.tmarg-info (erase-names-tel (tmarg-tel arginfo)) (tmarg-ty arginfo)

erase-names-tmext : TmExt → NMLS.TmExt
NMLS.TmExt.TmExtCode (erase-names-tmext 𝓉) = TmExt.TmExtCode 𝓉
NMLS.TmExt._≟tm-code_ (erase-names-tmext 𝓉) = TmExt._≟tm-code_ 𝓉
NMLS.TmExt.tm-code-ty (erase-names-tmext 𝓉) c = TmExt.tm-code-ty 𝓉 c
NMLS.TmExt.tm-code-arginfos (erase-names-tmext 𝓉) c = map erase-names-tmarg-info (TmExt.tm-code-arginfos 𝓉 c)
