open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.bProp.AlphaEquivalence.bPropExtension
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  where

open import Data.List
open import Data.String
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.Context ℳ 𝒯

open import Experimental.LogicalFramework.Parameter.bPropExtension ℳ 𝒯 String 𝓉
import Experimental.LogicalFramework.Parameter.bPropExtension ℳ 𝒯 ⊤ (erase-names-tmext 𝓉) as NMLS
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 String
import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 ⊤ as NMLSArg


erase-names-arg-info : ∀ {m} → ArgInfo m → NMLSArg.ArgInfo m
erase-names-arg-info info = NMLSArg.arginfo (erase-names-tel (arg-tel info))

erase-names-bpext : bPropExt → NMLS.bPropExt
NMLS.bPropExt.bPropExtCode (erase-names-bpext 𝒷) = bPropExt.bPropExtCode 𝒷
NMLS.bPropExt._≟bp-code_ (erase-names-bpext 𝒷) = bPropExt._≟bp-code_ 𝒷
NMLS.bPropExt.bp-code-tmarg-infos (erase-names-bpext 𝒷) c = map erase-names-tmarg-info (bPropExt.bp-code-tmarg-infos 𝒷 c)
NMLS.bPropExt.bp-code-bparg-infos (erase-names-bpext 𝒷) c = map erase-names-arg-info (bPropExt.bp-code-bparg-infos 𝒷 c)
