--------------------------------------------------
-- Reexporting the instance of MSTT for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.MSTT where

open import Applications.GuardedRecursion.MSTT.TypeExtension
open import Applications.GuardedRecursion.MSTT.TermExtension

open import Applications.GuardedRecursion.MSTT.ModeTheory public
open import Applications.GuardedRecursion.MSTT.Syntax.Type public
open import MSTT.Syntax.Context GR-mode-theory GR-ty-ext public
open import Applications.GuardedRecursion.MSTT.Syntax.Term public
open import MSTT.TCMonad public using (type-error ; ok)
open import MSTT.TypeChecker.ResultType GR-mode-theory GR-ty-ext public
open import MSTT.TypeChecker GR-mode-theory GR-ty-ext GR-tm-ext public
