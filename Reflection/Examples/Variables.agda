--------------------------------------------------
-- Some tests for the variable macro
--------------------------------------------------

open import Categories

module Reflection.Examples.Variables {C : Category} where

open import CwF-Structure
open import Types.Discrete
open import Types.Functions

test : Tm {C = C} (◇ ,, Bool') (Bool' [ π ])
test = var 0

test2 : Tm {C = C} (◇ ,, Bool' ,, (Nat' ⇛ Nat')) ((Nat' ⇛ Nat') [ π ])
test2 = var 0

test3 : Tm {C = C} (◇ ,, Bool' ,, Nat') ((Bool' [ π ]) [ π ])
test3 = var 1

id : ∀ {ℓ ℓ'} {Γ : Ctx C ℓ} {T : Ty Γ ℓ'} → Tm Γ (T ⇛ T)
id {Γ = Γ}{T = T} = lam T (var 0)
