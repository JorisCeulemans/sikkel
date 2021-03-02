--------------------------------------------------
-- Some instances for working with closed types and with the naturality solver
--------------------------------------------------

open import Categories

module Types.Instances {C : Category} where

open import CwF-Structure.Types
open import CwF-Structure.ClosedTypes
open import CwF-Structure.ContextFunctors
open import Reflection.Naturality.TypeOperations
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums


instance
  discr-closed : {A : Set} → IsClosedNatural {C} (Discr A)
  closed-natural {{discr-closed {A = A}}} = Discr-natural A

instance
--  discr-nul : {A : Set} → IsNullaryNatural {C} (Discr A)
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

instance
  fun-closed : {A B : ClosedType C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
               IsClosedNatural (A ⇛ B)
  closed-natural {{fun-closed}} σ = ≅ᵗʸ-trans (⇛-natural σ) (⇛-cong (closed-natural σ) (closed-natural σ))

  prod-closed : {A B : ClosedType C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
                IsClosedNatural (A ⊠ B)
  closed-natural {{prod-closed}} σ = ≅ᵗʸ-trans (⊠-natural σ) (⊠-cong (closed-natural σ) (closed-natural σ))

  sum-closed : {A B : ClosedType C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
               IsClosedNatural (A ⊞ B)
  closed-natural {{sum-closed}} σ = ≅ᵗʸ-trans (⊞-natural σ) (⊞-cong (closed-natural σ) (closed-natural σ))
