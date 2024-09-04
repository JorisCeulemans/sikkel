--------------------------------------------------
-- Reexporting the syntax for terms in parametric type theory
--   + definition of some synonyms.
--------------------------------------------------

open import Applications.BinaryParametricity.MSTT.TypeExtension.RelExtension

module Applications.BinaryParametricity.MSTT.Syntax.Term (rel-ext : RelExt) where

open import Data.Unit

open import Applications.BinaryParametricity.MSTT.ModeTheory
open import Applications.BinaryParametricity.MSTT.TypeExtension rel-ext
open import Applications.BinaryParametricity.MSTT.TermExtension rel-ext


import MSTT.Syntax.Term par-mode-theory par-ty-ext par-tm-ext as ParTerm
open ParTerm using (ext)
open ParTerm public hiding (ext)

pattern from-rel c a b r = ext (from-rel-code c a b r) tt
pattern from-rel1 c1 c2 f g r = ext (from-rel1-code c1 c2 f g r) tt
pattern from-rel2 c1 c2 c3 f g r = ext (from-rel2-code c1 c2 c3 f g r) tt
