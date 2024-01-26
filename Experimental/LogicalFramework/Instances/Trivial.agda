module Experimental.LogicalFramework.Instances.Trivial where

open import Data.Empty
open import Data.Maybe
open import Data.String
open import Data.Unit
open import Relation.Binary.PropositionalEquality

import Model.BaseCategory as M
import Model.DRA as DRA

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics
open import Experimental.LogicalFramework.MSTT.Parameter


record TrivMode : Set where
  constructor ★

triv-mt : ModeTheory
MTBasis.Mode (ModeTheory.mtb triv-mt) = TrivMode
MTBasis.NonTrivModality (ModeTheory.mtb triv-mt) _ _ = ⊥
MTBasis.mode-eq? (ModeTheory.mtb triv-mt) _ _ = just refl
MTBasis.non-triv-mod-eq? (ModeTheory.mtb triv-mt) () ()
MTBasis.⟦_⟧mode (ModeTheory.mtb triv-mt) ★ = M.★
MTBasis.⟦_⟧non-triv-mod (ModeTheory.mtb triv-mt) ()
MTComposition._ⓜnon-triv_ (ModeTheory.mtc triv-mt) () ()
MTComposition.⟦ⓜ⟧-non-triv-sound (ModeTheory.mtc triv-mt) () ()
MTCompositionLaws.mod-non-triv-assoc (ModeTheory.mtc-laws triv-mt) () () ()
MTTwoCell.TwoCell (ModeTheory.mt2 triv-mt) MTBasis.𝟙 MTBasis.𝟙 = ⊤
MTTwoCell.id-cell (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} = tt
MTTwoCell._ⓣ-vert_ (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} {ρ = MTBasis.𝟙} {κ = MTBasis.𝟙} _ _ = tt
MTTwoCell._ⓣ-hor_ (ModeTheory.mt2 triv-mt) {μ1 = MTBasis.𝟙} {MTBasis.𝟙} {MTBasis.𝟙} {MTBasis.𝟙} _ _ = tt
MTTwoCell.two-cell-eq? (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} {MTBasis.𝟙} tt tt = just refl
MTTwoCell.⟦_⟧two-cell (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} {MTBasis.𝟙} tt = DRA.id-cell

open ModeTheory triv-mt public hiding (id-cell)

-- The following type of id-cell works better with Agda's type inference
id-cell : TwoCell 𝟙 𝟙
id-cell = ModeTheory.id-cell triv-mt {μ = 𝟙}


triv-ty-ext : TyExt triv-mt
TyExt.TyExtCode triv-ty-ext _ _ = ⊥
TyExt._≟ty-code_ triv-ty-ext () ()
TyExt.show-ty-code triv-ty-ext ()
TyExt.⟦ triv-ty-ext ⟧ty-code ()
TyExt.sem-ty-code-natural triv-ty-ext ()

triv-tm-ext : TmExt triv-mt triv-ty-ext String
TmExt.TmExtCode triv-tm-ext _ = ⊥
TmExt._≟tm-code_ triv-tm-ext () ()
TmExt.tm-code-ty triv-tm-ext ()
TmExt.tm-code-arginfos triv-tm-ext ()

triv-tm-ext-sem : TmExtSem triv-mt triv-ty-ext (erase-names-tmext triv-mt triv-ty-ext triv-tm-ext)
TmExtSem.⟦ triv-tm-ext-sem ⟧tm-code ()


triv-mstt : MSTT-Parameter
MSTT-Parameter.ℳ triv-mstt = triv-mt
MSTT-Parameter.𝒯 triv-mstt = triv-ty-ext
MSTT-Parameter.𝓉 triv-mstt = triv-tm-ext
MSTT-Parameter.⟦𝓉⟧ triv-mstt = triv-tm-ext-sem
