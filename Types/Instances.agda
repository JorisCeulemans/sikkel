--------------------------------------------------
-- Some instances for working with closed types and with the naturality solver
--------------------------------------------------

open import Categories

module Types.Instances {C : Category} where

open import CwF-Structure.ClosedTypes
open import CwF-Structure.ContextFunctors
open import Reflection.Naturality.TypeOperations
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums


instance
  discr-closed : ∀ {ℓ} {A : Set ℓ} → IsClosedNatural {C} (Discr A)
  closed-natural {{discr-closed {A = A}}} = Discr-natural A

instance
--  discr-nul : ∀ {ℓ} {A : Set ℓ} → IsNullaryNatural {C} (Discr A)
--  discr-nul = discr-closed

  fun-bin : IsBinaryNatural {C} _⇛_
  natural-bin {{fun-bin}} σ = ⇛-natural σ
  cong-bin {{fun-bin}} = ⇛-cong

  prod-bin : IsBinaryNatural {C} _⊠_
  natural-bin {{prod-bin}} σ = ⊠-natural σ
  cong-bin {{prod-bin}} = ⊠-cong

  sum-bin : IsBinaryNatural {C} _⊞_
  natural-bin {{sum-bin}} σ = ⊞-natural σ
  cong-bin {{sum-bin}} = ⊞-cong
