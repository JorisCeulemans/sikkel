--------------------------------------------------
-- Reexporting the instance of MSTT for parametricity
--------------------------------------------------

open import Applications.BinaryParametricity.MSTT.TypeExtension.RelExtension

module Applications.BinaryParametricity.MSTT (rel-ext : RelExt) where

open import Applications.BinaryParametricity.MSTT.TypeExtension rel-ext
open import Applications.BinaryParametricity.MSTT.TermExtension rel-ext

open import Applications.BinaryParametricity.MSTT.ModeTheory public
open import Applications.BinaryParametricity.MSTT.Syntax.Type rel-ext public
open import MSTT.Syntax.Context par-mode-theory par-ty-ext public
open import Applications.BinaryParametricity.MSTT.Syntax.Term rel-ext public
open import MSTT.InterpretTypes par-mode-theory par-ty-ext public
open import MSTT.TCMonad public using (type-error ; ok)
open import MSTT.TypeChecker.ResultType par-mode-theory par-ty-ext public
open import MSTT.TypeChecker par-mode-theory par-ty-ext par-tm-ext public
open import MSTT.BasicOperations par-mode-theory par-ty-ext par-tm-ext public
