--------------------------------------------------
-- This module reexports everything that is related
-- to the different modalities for working with
-- guarded recursion. Moreover, it establishes the
-- 3 modalities as elements of the type Modality.
--------------------------------------------------

module GuardedRecursion.Modalities where

open import GuardedRecursion.Modalities.Later public
open import GuardedRecursion.Modalities.Timeless public
open import GuardedRecursion.Modalities.AllNow public
open import GuardedRecursion.Modalities.Interaction public
open import GuardedRecursion.Modalities.Instances public
open import GuardedRecursion.Modalities.Bundles public
