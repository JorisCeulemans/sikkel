--------------------------------------------------
-- Reexporting the syntax for types in guarded recursive type theory
--   + definition of some synonyms.
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.Syntax.Type where

open import Data.Product
open import Data.Unit

open import Applications.GuardedRecursion.MSTT.ModeTheory
open import Applications.GuardedRecursion.MSTT.TypeExtension


import MSTT.Syntax.Type GR-mode-theory GR-ty-ext as GRType
open GRType using (Ext)
open GRType public hiding (Ext)

▻ : TyExpr ω → TyExpr ω
▻ T = ⟨ later ∣ T ⟩

pattern GStream A = Ext GStream-code (A , tt)
