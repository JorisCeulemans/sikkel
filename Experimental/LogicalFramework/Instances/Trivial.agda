module Experimental.LogicalFramework.Instances.Trivial where

open import Data.Empty
open import Data.Maybe
open import Data.Unit
open import Relation.Binary.PropositionalEquality

import Model.BaseCategory as M
import Model.DRA as DRA

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionNormalization
open import Experimental.LogicalFramework.MSTT.Parameter


triv-mt : ModeTheory
MTMode.NonTrivMode (ModeTheory.mtm triv-mt) = ⊥
MTMode.non-triv-mode-eq? (ModeTheory.mtm triv-mt) _ _ = just refl
MTMode.⟦_⟧non-triv-mode (ModeTheory.mtm triv-mt) ()
MTModality.NonTrivModality (ModeTheory.mtμ triv-mt) _ _ = ⊥
MTModality.non-triv-mod-eq? (ModeTheory.mtμ triv-mt) () ()
MTModality.⟦_⟧non-triv-mod (ModeTheory.mtμ triv-mt) ()
MTComposition._ⓜnon-triv_ (ModeTheory.mtc triv-mt) () ()
MTComposition.⟦ⓜ⟧-non-triv-sound (ModeTheory.mtc triv-mt) () ()
MTCompositionLaws.mod-non-triv-assoc (ModeTheory.mtc-laws triv-mt) () () ()
MTTwoCell.TwoCell (ModeTheory.mt2 triv-mt) _ _ = ⊤
MTTwoCell.id-cell (ModeTheory.mt2 triv-mt) = tt
MTTwoCell._ⓣ-vert_ (ModeTheory.mt2 triv-mt) _ _ = tt
MTTwoCell._ⓣ-hor_ (ModeTheory.mt2 triv-mt) _ _ = tt
MTTwoCell.two-cell-eq? (ModeTheory.mt2 triv-mt) _ _ = just refl
MTTwoCell.⟦ ModeTheory.mt2 triv-mt ⟧two-cell {μ = MTModality.𝟙} {κ = MTModality.𝟙} _ = DRA.id-cell
MTTwoCellLaws.⟦id-cell⟧-sound (ModeTheory.mt2-laws triv-mt) {μ = MTModality.𝟙} = DRA.reflᵗᶜ
MTTwoCellLaws.⟦ⓣ-vert⟧-sound (ModeTheory.mt2-laws triv-mt) {μ = MTModality.𝟙} {κ = MTModality.𝟙} {ρ = MTModality.𝟙} _ _ =
  DRA.symᵗᶜ DRA.ⓣ-vert-unitˡ
MTTwoCellLaws.⟦ⓜ⟧-sound-natural (ModeTheory.mt2-laws triv-mt) {μ = MTModality.𝟙} {μ' = MTModality.𝟙} {ρ = MTModality.𝟙} {ρ' = MTModality.𝟙} _ _ =
  DRA.symᵗᶜ (DRA.𝟙-unitʳ-natural-to DRA.id-cell)
MTTwoCellLaws.⟦associator⟧ (ModeTheory.mt2-laws triv-mt) {μ = MTModality.𝟙} {ρ = MTModality.𝟙} MTModality.𝟙 =
  record { key-subst-eq = record { eq = λ _ → refl } }


open ModeTheory triv-mt public hiding (id-cell)

-- The following type of id-cell works better with Agda's type inference
id-cell : TwoCell {★} 𝟙 𝟙
id-cell = ModeTheory.id-cell triv-mt {m = ★} {μ = 𝟙}


triv-ty-ext : TyExt triv-mt
TyExt.TyExtCode triv-ty-ext _ _ = ⊥
TyExt._≟ty-code_ triv-ty-ext () ()
TyExt.show-ty-code triv-ty-ext ()
TyExt.⟦ triv-ty-ext ⟧ty-code ()
TyExt.sem-ty-code-natural triv-ty-ext ()

triv-tm-ext : TmExt triv-mt triv-ty-ext
TmExt.TmExtCode triv-tm-ext _ = ⊥
TmExt._≟tm-code_ triv-tm-ext () ()
TmExt.tm-code-ty triv-tm-ext ()
TmExt.tm-code-arginfos triv-tm-ext ()

triv-tm-ext-sem : TmExtSem triv-mt triv-ty-ext triv-tm-ext
TmExtSem.⟦ triv-tm-ext-sem ⟧tm-code ()
TmExtSem.⟦⟧tm-code-natural triv-tm-ext-sem ()
TmExtSem.⟦⟧tm-code-cong triv-tm-ext-sem ()

triv-tm-ext-norm : TmExtNormalization triv-mt triv-ty-ext triv-tm-ext triv-tm-ext-sem
TmExtNormalization.normalize-tm-code triv-tm-ext-norm _ () _


triv-mstt : MSTT-Parameter
MSTT-Parameter.ℳ triv-mstt = triv-mt
MSTT-Parameter.𝒯 triv-mstt = triv-ty-ext
MSTT-Parameter.𝓉 triv-mstt = triv-tm-ext
MSTT-Parameter.⟦𝓉⟧ triv-mstt = triv-tm-ext-sem
MSTT-Parameter.𝓉-norm triv-mstt = triv-tm-ext-norm



open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
open import Experimental.LogicalFramework.Parameter.ProofExtension
open import Experimental.LogicalFramework.Parameter


triv-bp-ext : bPropExt triv-mt triv-ty-ext triv-tm-ext
bPropExt.bPropExtCode triv-bp-ext _ = ⊥
bPropExt._≟bp-code_ triv-bp-ext () ()
bPropExt.bp-code-tmarg-infos triv-bp-ext ()
bPropExt.bp-code-bparg-infos triv-bp-ext ()

triv-bp-ext-sem : bPropExtSem triv-mt triv-ty-ext triv-tm-ext triv-bp-ext
bPropExtSem.⟦_⟧bp-code triv-bp-ext-sem ()
bPropExtSem.⟦⟧bp-code-natural triv-bp-ext-sem ()
bPropExtSem.⟦⟧bp-code-cong triv-bp-ext-sem ()

triv-pf-ext : ProofExt triv-mstt triv-bp-ext triv-bp-ext-sem
ProofExt.ProofExtCode triv-pf-ext _ = ⊥
ProofExt.pf-code-tmarg-infos triv-pf-ext ()
ProofExt.pf-code-bparg-infos triv-pf-ext ()
ProofExt.pf-code-pfarg-infos triv-pf-ext ()
ProofExt.pf-code-check triv-pf-ext ()

triv-param : BiSikkelParameter
BiSikkelParameter.𝒫 triv-param = triv-mstt
BiSikkelParameter.𝒷 triv-param = triv-bp-ext
BiSikkelParameter.⟦𝒷⟧ triv-param = triv-bp-ext-sem
BiSikkelParameter.𝓅 triv-param = triv-pf-ext
