--------------------------------------------------
-- Examples of STT programs and proofs of their properties
--------------------------------------------------

module Experimental.LogicalFramework.Example where

open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Experimental.LogicalFramework.MSTT
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Proof
-- open import Experimental.LogicalFramework.BetaReduction
open import Extraction

open import Model.BaseCategory hiding (★; ω)
import Model.CwF-Structure as M
import Model.Type.Constant as M
import Model.Type.Function as M
import Experimental.DependentTypes.Model.Function as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.ClosedTypes as M

private variable
  m : Mode
  Γ : Ctx m
  T : Ty m


--------------------------------------------------
-- Proving some properties of natural number addition

id : Tm Γ (T ⇛ T)
id = lam[ "x" ∈ _ ] svar "x"

plus : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
plus = nat-elim id (lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n"))))

{-
sem-plus : M.Tm (M.◇ {★}) ((M.Nat' M.⇛ M.Nat' M.⇛ M.Nat') M.[ _ ])
sem-plus = ⟦ plus {◇} ⟧tm

_+_ : ℕ → ℕ → ℕ
_+_ = extract-term ⟦ plus {◇} ⟧tm

_ : 16 + 9 ≡ 25
_ = refl
-}

-- ∀ n → plus n 0 = n
plus-zeroʳ : Formula Γ
plus-zeroʳ = ∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ svar "n" ∙ zero ≡ᶠ svar "n")

proof-plus-zeroʳ : {Γ : Ctx ★} → Proof Γ
proof-plus-zeroʳ = ∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] nat-induction "ind-hyp"
  (trans (id ∙ zero) (fun-cong nat-elim-β-zero zero) fun-β)
  (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ var' "n" {vsuc vzero} id-cell ∙ svar "n" ))) ∙ zero)
         (fun-cong (trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n")))) ∙ (plus ∙ svar "n"))
                          nat-elim-β-suc
                          fun-β) zero)
         (trans (suc ∙ (plus ∙ svar "n" ∙ zero))
                fun-β
                (cong suc (assumption' "ind-hyp" {𝟙} {𝟙} id-cell))))

test-plus-zeroʳ : {Ξ : ProofCtx ★} → check-proof Ξ proof-plus-zeroʳ plus-zeroʳ ≡ return _
test-plus-zeroʳ = refl


-- ∀ m n → plus m (suc n) = suc (plus m n)
plus-sucʳ : Formula Γ
plus-sucʳ = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus ∙ svar "m" ∙ (suc ∙ svar "n") ≡ᶠ suc ∙ (plus ∙ svar "m" ∙ svar "n")))

proof-plus-sucʳ : {Γ : Ctx ★} → Proof Γ
proof-plus-sucʳ = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp"
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans (id ∙ (suc ∙ svar "n")) (fun-cong nat-elim-β-zero (suc ∙ svar "n")) (trans (suc ∙ svar "n") fun-β (sym (cong suc (trans (id ∙ svar "n") (fun-cong nat-elim-β-zero (svar "n")) fun-β)))))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n")))) ∙ (plus ∙ svar "m") ∙ (suc ∙ svar "n"))
                                   (fun-cong nat-elim-β-suc (suc ∙ svar "n"))
                                   (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ svar "m" ∙ svar "n"))) ∙ (suc ∙ svar "n"))
                                          (fun-cong fun-β (suc ∙ svar "n"))
                                          (trans (suc ∙ (plus ∙ svar "m" ∙ (suc ∙ svar "n")))
                                                 fun-β
                                                 (cong suc (trans (suc ∙ (plus ∙ svar "m" ∙ svar "n"))
                                                                  (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ svar "m" ∙ (suc ∙ svar "n") ≡ᶠ suc ∙ (plus ∙ svar "m" ∙ svar "n")) (assumption' "ind-hyp" {𝟙} {𝟙} id-cell) (svar "n"))
                                                                  (sym (trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n")))) ∙ (plus ∙ svar "m") ∙ svar "n")
                                                                              (fun-cong nat-elim-β-suc (svar "n"))
                                                                              (trans ((lam[ "n" ∈ Nat' ] suc ∙ (plus ∙ svar "m" ∙ svar "n")) ∙ svar "n")
                                                                                     (fun-cong fun-β (svar "n"))
                                                                                     fun-β))))))))


test-plus-sucʳ : {Ξ : ProofCtx ★} → check-proof Ξ proof-plus-sucʳ plus-sucʳ ≡ return _
test-plus-sucʳ = refl


-- ∀ m n → plus m n = plus n m
plus-comm : Formula Γ
plus-comm = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus ∙ svar "m" ∙ svar "n" ≡ᶠ plus ∙ svar "n" ∙ svar "m"))

proof-plus-comm : {Γ : Ctx ★} → Proof Γ
proof-plus-comm = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp"
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans (id ∙ svar "n") (fun-cong nat-elim-β-zero (svar "n")) (trans (svar "n") fun-β (sym (∀-elim 𝟙 plus-zeroʳ proof-plus-zeroʳ (svar "n")))))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] lam[ "n" ∈ Nat' ] suc ∙ (svar "f" ∙ svar "n")) ∙ (plus ∙ svar "m") ∙ svar "n")
                                   (fun-cong nat-elim-β-suc (svar "n"))
                                   (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ svar "m" ∙ svar "n"))) ∙ svar "n")
                                          (fun-cong fun-β (svar "n"))
                                          (trans (suc ∙ (plus ∙ svar "m" ∙ svar "n")) fun-β
                                            (trans (suc ∙ (plus ∙ svar "n" ∙ svar "m"))
                                                   (cong suc (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ svar "m" ∙ svar "n" ≡ᶠ plus ∙ svar "n" ∙ svar "m")) (assumption' "ind-hyp" {𝟙} {𝟙} id-cell) (svar "n")))
                                                   (sym (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ var' "n" {vsuc vzero} id-cell ∙ (suc ∙ svar "n") ≡ᶠ suc ∙ (plus ∙ var' "n" {vsuc vzero} id-cell ∙ svar "n"))) (∀-elim 𝟙 plus-sucʳ proof-plus-sucʳ (svar "n")) (svar "m")))))))

test-plus-comm : {Ξ : ProofCtx ★} → check-proof Ξ proof-plus-comm plus-comm ≡ return _
test-plus-comm = refl


--------------------------------------------------
-- Tests for α-equivalence
{-
α-test : [] ⊢ (lam[ "x" ∈ Bool' ] (lam[ "f" ∈ Bool' ⇛ Bool' ] var "f" ∙ var "x"))
                ≡ᶠ (lam[ "b" ∈ Bool' ] (lam[ "g" ∈ Bool' ⇛ Bool' ] var "g" ∙ var "b"))
α-test = refl

α-test2 : [] ⊢ ∀[ "b" ∈ Bool' ] ((lam[ "x" ∈ Bool' ] (lam[ "f" ∈ Bool' ⇛ Bool' ] var "f" ∙ var "x")) ∙ var "b")
                                       ≡ᶠ (lam[ "g" ∈ Bool' ⇛ Bool' ] var "g" ∙ var "b")
α-test2 = ∀-intro (withTmAlpha fun-β)

α-test3 : [] ⊢ (∀[ "n" ∈ Nat' ] var "n" ≡ᶠ var "n")
                 ⊃ (∀[ "m" ∈ Nat' ] var "m" ≡ᶠ var "m")
α-test3 = assume[ "reflexivity" ] withAlpha (assumption "reflexivity")

α-test4 : [] ⊢ (∀[ "n" ∈ Nat' ] (lam[ "m" ∈ Nat' ] var "n") ≡ᶠ (lam[ "n" ∈ Nat' ] var "n"))
                 ⊃ (∀[ "m" ∈ Nat' ] (lam[ "n" ∈ Nat' ] var "m") ≡ᶠ lam[ "x" ∈ Nat' ] var "x")
α-test4 = assume[ "silly assumption" ] withAlpha (assumption "silly assumption")
-}
