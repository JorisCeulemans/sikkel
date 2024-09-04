--------------------------------------------------
-- Reexporting the syntax for types in parametric type theory
--   + definition of some synonyms.
--------------------------------------------------

open import Applications.BinaryParametricity.MSTT.TypeExtension.RelExtension

module Applications.BinaryParametricity.MSTT.Syntax.Type (rel-ext : RelExt) where

open import Data.Product
open import Data.Unit

open import Applications.BinaryParametricity.MSTT.ModeTheory
open import Applications.BinaryParametricity.MSTT.TypeExtension rel-ext


import MSTT.Syntax.Type par-mode-theory par-ty-ext as GRType
open GRType using (Ext)
open GRType public hiding (Ext)

pattern FromRel c = Ext (FromRel-code c) tt
