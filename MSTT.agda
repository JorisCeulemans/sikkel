--------------------------------------------------
-- Reexporting definitions needed to use MSTT in Agda
--   This module needs to be instantiated with the necessary records
--   that define the mode theory, and type and term extensions
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension
open import MSTT.Parameter.TermExtension

module MSTT (mt : ModeTheory) (ty-ext : TyExt mt) (tm-ext : TmExt mt ty-ext) where

open import MSTT.TCMonad public using (ok; type-error)

open import MSTT.Syntax.Type mt ty-ext public
open import MSTT.Syntax.Context mt ty-ext public
open import MSTT.Syntax.Term mt ty-ext tm-ext public

open import MSTT.TypeChecker mt ty-ext tm-ext public

open import MSTT.BasicOperations mt ty-ext tm-ext public
