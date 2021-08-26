module Experimental.DeepEmbedding.GuardedRecursion.ModalityInteractionTest where

open import Categories renaming (★ to ′★; ω to ′ω)
open import CwF-Structure hiding (_,,_; var) renaming (◇ to ′◇)
open import Types.Discrete renaming (Nat' to ′Nat'; Bool' to ′Bool')
open import Modalities hiding (_ⓜ_; _,lock⟨_⟩; mod-intro; mod-elim) renaming (⟨_∣_⟩ to ′⟨_∣_⟩; 𝟙 to ′𝟙)
open import GuardedRecursion.Modalities hiding (timeless; allnow; later; ▻'; next'; _⊛'_; löb)

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker


-- This example shows that the verified typechecker supports a wide range of
--   definitional equalities of modalities. Its modality solver takes care of
--   associativity of composition, the identity laws for e-𝟙 and the equalities
--   `allnow ⓜ timeless ≅ᵐ 𝟙` and `allnow ⓜ later ≅ᵐ allnow` which are specific
--   for guarded recursion.
allnow-timeless-test-expr : TmExpr ★
allnow-timeless-test-expr = ann (mod-intro (allnow ⓜ timeless) (lit 0)) ∈ ⟨ 𝟙 ∣ Nat' ⟩

allnow-timeless-test : Tm {C = ′★} ′◇ ′⟨ ′𝟙 ∣ ′Nat' ⟩
allnow-timeless-test = ⟦ allnow-timeless-test-expr ⟧tm-in ◇

-- This example shows that the typechecker now also supports type equalities
--   such as `mod μ (mod ρ T) ≅ᵗʸ mod (μ ⓜ ρ) T`.
combined-test-expr : TmExpr ★
combined-test-expr = ann (mod-intro allnow (mod-intro timeless (lit 0))) ∈ Nat'

combined-test : Tm {C = ′★} ′◇ ′Nat'
combined-test = ⟦ combined-test-expr ⟧tm-in ◇
