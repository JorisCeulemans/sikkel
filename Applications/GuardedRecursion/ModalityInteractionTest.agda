module Applications.GuardedRecursion.ModalityInteractionTest where

open import Model.BaseCategory renaming (★ to ′★; ω to ′ω)
open import Model.CwF-Structure renaming (◇ to ′◇)
open import Model.Type.Discrete renaming (Nat' to ′Nat'; Bool' to ′Bool')
open import Model.Modality hiding (_ⓜ_; _,lock⟨_⟩; mod-intro; mod-elim) renaming (⟨_∣_⟩ to ′⟨_∣_⟩; 𝟙 to ′𝟙)
open import Applications.GuardedRecursion.Model.Modalities hiding (constantly; forever; later; ▻'; next'; _⊛'_; löb)

open import Applications.GuardedRecursion.MSTT


-- This example shows that the verified typechecker supports a wide range of
--   definitional equalities of modalities. Its modality solver takes care of
--   associativity of composition, the identity laws for e-𝟙 and the equalities
--   `forever ⓜ constantly ≅ᵐ 𝟙` and `forever ⓜ later ≅ᵐ forever` which are specific
--   for guarded recursion.
forever-constantly-test-expr : TmExpr ★
forever-constantly-test-expr = ann (mod-intro (forever ⓜ constantly) (lit 0)) ∈ ⟨ 𝟙 ∣ Nat' ⟩

forever-constantly-test : Tm {C = ′★} ′◇ ′⟨ ′𝟙 ∣ ′Nat' ⟩
forever-constantly-test = ⟦ forever-constantly-test-expr ⟧tm-in ◇

-- This example shows that the typechecker now also supports type equalities
--   such as `mod μ (mod ρ T) ≅ᵗʸ mod (μ ⓜ ρ) T`.
combined-test-expr : TmExpr ★
combined-test-expr = ann (mod-intro forever (mod-intro constantly (lit 0))) ∈ Nat'

combined-test : Tm {C = ′★} ′◇ ′Nat'
combined-test = ⟦ combined-test-expr ⟧tm-in ◇
