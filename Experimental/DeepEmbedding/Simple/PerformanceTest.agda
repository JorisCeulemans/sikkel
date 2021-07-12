module Experimental.DeepEmbedding.Simple.PerformanceTest where

open import Data.Bool
open import Data.Fin
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Experimental.DeepEmbedding.Simple.TypeChecker {C = ★}
open import Translation

test1 : TmExpr 0
test1 = e-lam e-bool (e-var zero)

⟦test1⟧sikkel : Tm ◇ (Bool' ⇛ Bool')
⟦test1⟧sikkel = ⟦ test1 ⟧tm-in e-◇

⟦test1⟧agda : Bool → Bool
⟦test1⟧agda = translate-term ⟦test1⟧sikkel

test-test1 : {b1 : Bool} → ⟦test1⟧agda b1 ≡ b1
test-test1 = refl

test2 : TmExpr 0
test2 = e-lam e-bool (e-lam e-bool (e-var zero))

⟦test2⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool')
⟦test2⟧sikkel = ⟦ test2 ⟧tm-in e-◇

⟦test2⟧agda : Bool → Bool → Bool
⟦test2⟧agda = translate-term ⟦test2⟧sikkel

test-test2 : {b1 b2 : Bool} → ⟦test2⟧agda b1 b2 ≡ b2
test-test2 = refl

test3 : TmExpr 0
test3 = e-lam e-bool (e-lam e-bool (e-lam e-bool (e-var zero)))

⟦test3⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
⟦test3⟧sikkel = ⟦ test3 ⟧tm-in e-◇

⟦test3⟧agda : Bool → Bool → Bool → Bool
⟦test3⟧agda = translate-term ⟦test3⟧sikkel

test-test3 : {b1 b2 b3 : Bool} → ⟦test3⟧agda b1 b2 b3 ≡ b3
test-test3 = refl

test4 : TmExpr 0
test4 = e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-var zero))))

⟦test4⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
⟦test4⟧sikkel = ⟦ test4 ⟧tm-in e-◇

⟦test4⟧agda : Bool → Bool → Bool → Bool → Bool
⟦test4⟧agda = translate-term ⟦test4⟧sikkel

test-test4 : {b1 b2 b3 b4 : Bool} → ⟦test4⟧agda b1 b2 b3 b4 ≡ b4
test-test4 = refl

test5 : TmExpr 0
test5 = e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-var zero)))))

⟦test5⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
⟦test5⟧sikkel = ⟦ test5 ⟧tm-in e-◇

⟦test5⟧agda : Bool → Bool → Bool → Bool → Bool → Bool
⟦test5⟧agda = translate-term ⟦test5⟧sikkel

test-test5 : {b1 b2 b3 b4 b5 : Bool} → ⟦test5⟧agda b1 b2 b3 b4 b5 ≡ b5
test-test5 = refl

test6 : TmExpr 0
test6 = e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-var zero))))))

⟦test6⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
⟦test6⟧sikkel = ⟦ test6 ⟧tm-in e-◇

⟦test6⟧agda : Bool → Bool → Bool → Bool → Bool → Bool → Bool
⟦test6⟧agda = translate-term ⟦test6⟧sikkel

test-test6 : {b1 b2 b3 b4 b5 b6 : Bool} → ⟦test6⟧agda b1 b2 b3 b4 b5 b6 ≡ b6
test-test6 = refl

test7 : TmExpr 0
test7 = e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-var zero)))))))

⟦test7⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
⟦test7⟧sikkel = ⟦ test7 ⟧tm-in e-◇

⟦test7⟧agda : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool
⟦test7⟧agda = translate-term ⟦test7⟧sikkel

test-test7 : {b1 b2 b3 b4 b5 b6 b7 : Bool} → ⟦test7⟧agda b1 b2 b3 b4 b5 b6 b7 ≡ b7
test-test7 = refl

test8 : TmExpr 0
test8 = e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-lam e-bool (e-var zero))))))))

⟦test8⟧sikkel : Tm ◇ (Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool' ⇛ Bool')
⟦test8⟧sikkel = ⟦ test8 ⟧tm-in e-◇

⟦test8⟧agda : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool
⟦test8⟧agda = translate-term ⟦test8⟧sikkel

test-test8 : {b1 b2 b3 b4 b5 b6 b7 b8 : Bool} → ⟦test8⟧agda b1 b2 b3 b4 b5 b6 b7 b8 ≡ b8
test-test8 = refl
