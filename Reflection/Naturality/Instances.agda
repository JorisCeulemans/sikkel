{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Some instances for working with the naturality solver
--
-- Note: The option omega-in-omega is used here in order to work with
-- Setω as a valid sort (which is not possible in Agda 2.6.1 without
-- this option). This code should typecheck without this option in Agda 2.6.2
-- once released.
-- Note 2: The instances defined in this file will eventually be moved
-- to the files in which the respective types/type operations are defined.
-- However, we do not want to use the option omega-in-omega there.
--------------------------------------------------

open import Categories

module Reflection.Naturality.Instances {C : Category} where

open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums
open import Reflection.Naturality


instance
  discr-nul : ∀ {A : Set} → IsNullaryNatural {C} (Discr A)
  natural-nul {{discr-nul {A = A}}} σ = Discr-natural A σ

  fun-bin : IsBinaryNatural {C} _⇛_
  natural-bin {{fun-bin}} σ = ⇛-natural σ
  cong-bin {{fun-bin}} = ⇛-cong

  prod-bin : IsBinaryNatural {C} _⊠_
  natural-bin {{prod-bin}} σ = ⊠-natural σ
  cong-bin {{prod-bin}} = ⊠-cong

  sum-bin : IsBinaryNatural {C} _⊞_
  natural-bin {{sum-bin}} σ = ⊞-natural σ
  cong-bin {{sum-bin}} = ⊞-cong
