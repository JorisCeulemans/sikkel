open import Categories

module Performance.ContextTest {C : Category} where

open import Data.Bool

open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Instances
open import Reflection.Tactic.Lambda


test1 : Tm {C = C} ◇ (Bool' ⇛ Bool')
test1 = lamι[ "x1" ∈ Bool' ]
          varι "x1"

test2 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool')
test2 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            varι "x2"

test3 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test3 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            lamι[ "x3" ∈ Bool' ]
              varι "x3"

test4 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test4 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            lamι[ "x3" ∈ Bool' ]
              lamι[ "x4" ∈ Bool' ]
                varι "x4"

test5 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test5 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            lamι[ "x3" ∈ Bool' ]
              lamι[ "x4" ∈ Bool' ]
                lamι[ "x5" ∈ Bool' ]
                  varι "x5"

test6 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test6 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            lamι[ "x3" ∈ Bool' ]
              lamι[ "x4" ∈ Bool' ]
                lamι[ "x5" ∈ Bool' ]
                  lamι[ "x6" ∈ Bool' ]
                    varι "x6"

test7 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test7 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            lamι[ "x3" ∈ Bool' ]
              lamι[ "x4" ∈ Bool' ]
                lamι[ "x5" ∈ Bool' ]
                  lamι[ "x6" ∈ Bool' ]
                    lamι[ "x7" ∈ Bool' ]
                      varι "x7"

test8 : Tm {C = C} ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
test8 = lamι[ "x1" ∈ Bool' ]
          lamι[ "x2" ∈ Bool' ]
            lamι[ "x3" ∈ Bool' ]
              lamι[ "x4" ∈ Bool' ]
                lamι[ "x5" ∈ Bool' ]
                  lamι[ "x6" ∈ Bool' ]
                    lamι[ "x7" ∈ Bool' ]
                      lamι[ "x8" ∈ Bool' ]
                        varι "x8"
