module Experimental.LogicalFramework.ModeTheory.Trivial where

open import Data.Empty
open import Data.Maybe
open import Data.Unit
open import Relation.Binary.PropositionalEquality

import Model.BaseCategory as M
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics


data TrivMode : Set where
  ★ : TrivMode

triv-mt : ModeTheory
MTBasis.Mode (ModeTheory.mtb triv-mt) = TrivMode
MTBasis.NonTrivModality (ModeTheory.mtb triv-mt) _ _ = ⊥
MTBasis.mode-eq? (ModeTheory.mtb triv-mt) ★ ★ = just refl
MTBasis.non-triv-mod-eq? (ModeTheory.mtb triv-mt) () ()
MTComposition._ⓜnon-triv_ (ModeTheory.mtc triv-mt) () ()
MTCompositionLaws.mod-non-triv-assoc (ModeTheory.mtc-laws triv-mt) () () ()
MTTwoCell.TwoCell (ModeTheory.mt2 triv-mt) MTBasis.𝟙 MTBasis.𝟙 = ⊤
MTTwoCell.id-cell (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} = tt
MTTwoCell._ⓣ-vert_ (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} {ρ = MTBasis.𝟙} {κ = MTBasis.𝟙} _ _ = tt
MTTwoCell._ⓣ-hor_ (ModeTheory.mt2 triv-mt) {μ1 = MTBasis.𝟙} {MTBasis.𝟙} {MTBasis.𝟙} {MTBasis.𝟙} _ _ = tt
MTTwoCell.two-cell-eq? (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} {MTBasis.𝟙} tt tt = just refl

open ModeTheory triv-mt public

⟦triv-mt⟧ : ModeTheorySemantics triv-mt
MTSemBasis.⟦ ModeTheorySemantics.mtsb ⟦triv-mt⟧ ⟧mode ★ = M.★
MTSemBasis.⟦ ModeTheorySemantics.mtsb ⟦triv-mt⟧ ⟧non-triv-mod ()
MTSemCompletion.⟦ⓜ⟧-non-triv-sound (ModeTheorySemantics.mtsc ⟦triv-mt⟧) () ()
MTSemCompletion.⟦ ModeTheorySemantics.mtsc ⟦triv-mt⟧ ⟧two-cell {μ = MTBasis.𝟙} {MTBasis.𝟙} tt = M.id-cell

open ModeTheorySemantics ⟦triv-mt⟧ public
