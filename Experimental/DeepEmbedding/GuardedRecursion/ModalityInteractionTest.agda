module Experimental.DeepEmbedding.GuardedRecursion.ModalityInteractionTest where

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Modalities
open Modality
open import GuardedRecursion.Modalities

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker


-- This example shows that the verified typechecker supports a wide range of
--   definitional equalities of modalities. Its modality solver takes care of
--   associativity of composition, the identity laws for e-𝟙 and the equalities
--   `allnow ⓜ timeless ≅ᵐ 𝟙` and `allnow ⓜ later ≅ᵐ allnow` which are specific
--   for guarded recursion.
allnow-timeless-test-expr : TmExpr e-★
allnow-timeless-test-expr = e-ann (e-mod-intro (e-allnow e-ⓜ e-timeless) (e-lit 0)) ∈ e-mod e-𝟙 e-Nat

allnow-timeless-test : Tm {C = ★} ◇ (mod 𝟙 Nat')
allnow-timeless-test = ⟦ allnow-timeless-test-expr ⟧tm-in e-◇

-- This example shows that the typechecker now also supports type equalities
--   such as `mod μ (mod ρ T) ≅ᵗʸ mod (μ ⓜ ρ) T`.
combined-test-expr : TmExpr e-★
combined-test-expr = e-ann (e-mod-intro e-allnow (e-mod-intro e-timeless (e-lit 0))) ∈ e-Nat

combined-test : Tm {C = ★} ◇ Nat'
combined-test = ⟦ combined-test-expr ⟧tm-in e-◇
