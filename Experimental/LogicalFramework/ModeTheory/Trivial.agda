module Experimental.LogicalFramework.ModeTheory.Trivial where

open import Data.Empty
open import Data.Maybe
open import Data.Unit
open import Relation.Binary.PropositionalEquality

import Model.BaseCategory as M
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory


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
MTTwoCell.⟦_⟧two-cell (ModeTheory.mt2 triv-mt) {μ = MTBasis.𝟙} {MTBasis.𝟙} tt = M.id-cell

open ModeTheory triv-mt public hiding (id-cell)

-- The following type of id-cell works better with Agda's type inference
id-cell : TwoCell 𝟙 𝟙
id-cell = ModeTheory.id-cell triv-mt {μ = 𝟙}
