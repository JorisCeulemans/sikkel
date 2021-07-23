module Experimental.DeepEmbedding.GuardedRecursion.ModalityInteractionTest where

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Modalities
open Modality
open import GuardedRecursion.Modalities

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker


-- The following test currently fails because the typechecker does not yet deal
--   well with equality of modalities. At the moment, modalities are only considered
--   equal if they are really identical. In a future update of the typechecker, we
--   will add more equalities, such as associativity of composition, the unit modality
--   being a unit for composition and the specific equalities allnow ⓜ timeless ≅ᵐ 𝟙
--   and allnow ⓜ later ≅ᵐ allnow.
allnow-timeless-test-expr : TmExpr e-★
allnow-timeless-test-expr = e-ann (e-mod-intro (e-allnow e-ⓜ e-timeless) (e-lit 0)) ∈ e-mod e-𝟙 e-Nat

allnow-timeless-test : Tm {C = ★} ◇ (mod 𝟙 Nat')
allnow-timeless-test = {!⟦ allnow-timeless-test-expr ⟧tm-in e-◇!}


-- Same remark as above. Here we additionally need to extend the function checking
--   type equality to include equalities such as mod 𝟙 T ≅ᵗʸ T and
--   mod μ (mod ρ T) ≅ᵗʸ mod (μ ⓜ ρ) T (up to certain substitutions).
combined-test-expr : TmExpr e-★
combined-test-expr = e-ann (e-mod-intro e-allnow (e-mod-intro e-timeless (e-lit 0))) ∈ e-Nat

combined-test : Tm {C = ★} ◇ Nat'
combined-test = {!⟦ combined-test-expr ⟧tm-in e-◇!}
