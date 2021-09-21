--------------------------------------------------
-- Some instances for the naturality solver to work with guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Instances where

open import Categories
open import CwF-Structure
open import Reflection.Naturality.TypeOperations
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.AllNow


instance
  ▻'-un : IsUnaryNatural ▻'
  natural-un {{▻'-un}} = ▻'-natural
  cong-un {{▻'-un}} = ▻'-cong

  ▻-un : IsUnaryNatural ▻
  natural-un {{▻-un}} = ▻-natural
  cong-un {{▻-un}} = ▻-cong

  timeless-ty-un : IsUnaryNatural timeless-ty
  IsUnaryNatural.natural-un timeless-ty-un = λ σ → timeless-ty-natural σ
  IsUnaryNatural.cong-un timeless-ty-un = timeless-ty-cong

  allnow-ty-un : IsUnaryNatural allnow-ty
  IsUnaryNatural.natural-un allnow-ty-un = λ σ → allnow-ty-natural σ
  IsUnaryNatural.cong-un allnow-ty-un = allnow-ty-cong
