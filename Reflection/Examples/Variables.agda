--------------------------------------------------
-- Some tests for the variable macros
--------------------------------------------------

open import Categories

module Reflection.Examples.Variables {C : Category} where

open import CwF-Structure
open import Types.Discrete
open import Types.Functions


test : Tm {C = C} (◇ ,, Bool') (Bool' [ π ])
test = db-var 0

test2 : Tm {C = C} (◇ ,, Bool' ,, (Nat' ⇛ Nat')) ((Nat' ⇛ Nat') [ π ])
test2 = db-var 0

test3 : Tm {C = C} (◇ ,, Bool' ,, Nat') ((Bool' [ π ]) [ π ])
test3 = db-var 1

id : {Γ : Ctx C} {T : Ty Γ} → Tm Γ (T ⇛ T)
id {Γ = Γ}{T = T} = lam T (db-var 0)

test4 : Tm {C = C} (◇ ,, "x" ∈ Bool') (Bool' [ π ])
test4 = var "x"

test5 : Tm {C = C} (◇ ,, "x" ∈ Bool' ,, "y" ∈ (Nat' ⇛ Nat')) ((Nat' ⇛ Nat') [ π ])
test5 = var "y"

test6 : Tm {C = C} (◇ ,, "x" ∈ Bool' ,, "y" ∈ Nat') ((Bool' [ π ]) [ π ])
test6 = var "x"

id2 : {Γ : Ctx C} {T : Ty Γ} → Tm Γ (T ⇛ T)
id2 {Γ = Γ}{T = T} = lam[ "x" ∈ T ] var "x"
