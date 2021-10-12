--------------------------------------------------
-- Reexporting the instance of MSTT for parametricity
--------------------------------------------------

open import Applications.Parametricity.MSTT.TypeExtension.RelExtension

module Applications.Parametricity.MSTT (rel-ext : RelExt) where

open import Applications.Parametricity.MSTT.TypeExtension rel-ext
open import Applications.Parametricity.MSTT.TermExtension rel-ext

open import Applications.Parametricity.MSTT.ModeTheory public
open import Applications.Parametricity.MSTT.Syntax.Type rel-ext public
open import MSTT.Syntax.Context par-mode-theory par-ty-ext public
open import Applications.Parametricity.MSTT.Syntax.Term rel-ext public
open import MSTT.TCMonad public using (type-error ; ok)
open import MSTT.TypeChecker.ResultType par-mode-theory par-ty-ext public
open import MSTT.TypeChecker par-mode-theory par-ty-ext par-tm-ext public
