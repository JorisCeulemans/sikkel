--------------------------------------------------
-- Reexporting the syntax for types in guarded recursive type theory
--   + definition of some synonyms.
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.Syntax.Type where

open import Data.Product
open import Data.String
open import Data.Unit

open import Applications.GuardedRecursion.MSTT.ModeTheory
open import Applications.GuardedRecursion.MSTT.TypeExtension
open import MSTT.TCMonad


import MSTT.Syntax.Type GR-mode-theory GR-ty-ext as GRType
open GRType using (Ext)
open GRType public hiding (Ext)

▻ : TyExpr ω → TyExpr ω
▻ T = ⟨ later ∣ T ⟩

pattern GStream A = Ext GStream-code (A , tt)


data IsGStream : TyExpr ω → Set where
  gstr-ty :  (A : TyExpr ★) → IsGStream (GStream A)

is-gstr-ty : (T : TyExpr ω) → TCM (IsGStream T)
is-gstr-ty (GStream A) = return (gstr-ty A)
is-gstr-ty T = type-error ("Expected a guarded stream but received instead: " ++ show-type T)
