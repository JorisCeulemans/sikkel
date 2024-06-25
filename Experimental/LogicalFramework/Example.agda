--------------------------------------------------
-- Examples of MSTT programs and proofs of their properties
--------------------------------------------------

module Experimental.LogicalFramework.Example where

open import Data.List
open import Data.Nat hiding (_+_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Experimental.LogicalFramework.Instances.Trivial
open import Experimental.LogicalFramework.MSTT triv-mstt
open import Experimental.LogicalFramework triv-param
open import Extraction

open import Model.BaseCategory hiding (★; ω)
import Model.CwF-Structure as M
import Model.Type.Constant as M
import Model.Type.Function as M
import Experimental.DependentTypes.Model.Function as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

private variable
  Γ Δ : Ctx ★
  T : Ty ★


--------------------------------------------------
-- Proving some properties of natural number addition

id : Tm Γ (T ⇛ T)
id = lam[ "x" ∈ _ ] svar "x"

plus-helper : Tm Γ ((Nat' ⇛ Nat') ⇛ Nat' ⇛ Nat')
plus-helper = lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] suc (svar "f" ∙ svar "n"))

plus' : Tm Γ Nat' → Tm Γ (Nat' ⇛ Nat')
plus' m = nat-rec id plus-helper m

plus : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
plus = lam[ "m" ∈ Nat' ] plus' (svar "m")

sem-plus : M.Tm M.◇ (M.Nat' M.⇛ M.Nat' M.⇛ M.Nat')
sem-plus = ⟦ plus {Γ = ◇ {★}} ⟧tm

{-
_+_ : ℕ → ℕ → ℕ
_+_ = extract-term {!!} {!!} -- extract-term ? sem-plus

_ : 16 + 9 ≡ 25
_ = refl
-}

-- ∀ n → plus n 0 = n
plus-zeroʳ : bProp Γ
plus-zeroʳ = ∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus' (svar "n") ∙ zero ≡ᵇ svar "n")

suc' : Tm Γ (Nat' ⇛ Nat')
suc' = lam[ "n" ∈ Nat' ] suc (svar "n")

cong-suc : {Γ : Ctx ★} (m n : Tm Γ Nat') → Proof (Γ ,lock⟨ 𝟙 ⟩) → Proof Γ
cong-suc m n p = trans (suc' ∙¹ m) by-normalization (trans (suc' ∙¹ n) (cong suc' p) by-normalization)

proof-plus-zeroʳ : {Γ : Ctx ★} → Proof Γ
proof-plus-zeroʳ {Γ = Γ} =
  ∀-intro[ 𝟙 ∣ "n" ∈ Nat' ]
  (nat-induction "ind-hyp"
    by-normalization
    (trans (suc (plus' (svar "n") ∙ zero))
           by-normalization
           (cong-suc (plus' (svar "n") ∙ zero) (svar "n") (assumption' "ind-hyp" {𝟙} {𝟙} id-cell))))

test-plus-zeroʳ : (PCResult.goals <$> check-proof ◇ proof-plus-zeroʳ plus-zeroʳ) ≡ ok []
test-plus-zeroʳ = refl


-- ∀ m n → plus m (suc n) = suc (plus m n)
plus-sucʳ : bProp Γ
plus-sucʳ = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus' (svar "m") ∙ suc (svar "n") ≡ᵇ suc (plus' (svar "m") ∙ svar "n")))

proof-plus-sucʳ : {Γ : Ctx ★} → Proof Γ
proof-plus-sucʳ = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp"
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] by-normalization)
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ]
    (trans (suc (plus' (svar "m") ∙ suc (svar "n")))
           by-normalization
           (cong-suc (plus' (svar "m") ∙ suc (svar "n")) (plus' (suc (svar "m")) ∙ svar "n")
             (trans (suc (plus' (svar "m") ∙ svar "n"))
                    (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus' (svar "m") ∙ suc (svar "n") ≡ᵇ suc (plus' (svar "m") ∙ svar "n"))
                              (assumption' "ind-hyp" {𝟙} {𝟙} id-cell) (svar "n"))
                    by-normalization))))

test-plus-sucʳ : (PCResult.goals <$> check-proof ◇ proof-plus-sucʳ plus-sucʳ) ≡ ok []
test-plus-sucʳ = refl


-- ∀ m n → plus m n = plus n m
plus-comm : bProp Γ
plus-comm = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus' (svar "m") ∙ svar "n" ≡ᵇ plus' (svar "n") ∙ svar "m"))

proof-plus-comm : {Γ : Ctx ★} → Proof Γ
proof-plus-comm = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp"
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans (svar "n") by-normalization (sym (∀-elim 𝟙 plus-zeroʳ proof-plus-zeroʳ (svar "n"))))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ]
    trans (suc (plus' (svar "m") ∙ svar "n"))
          by-normalization
          (trans (suc (plus' (svar "n") ∙ svar "m"))
                 (cong-suc (plus' (svar "m") ∙ svar "n")
                           (plus' (svar "n") ∙ svar "m")
                           (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus' (svar "m") ∙ svar "n" ≡ᵇ plus' (svar "n") ∙ svar "m")
                                     (assumption' "ind-hyp" {𝟙} {𝟙} id-cell) (svar "n")))
                 (sym (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus' (var' "n" {vsuc (vzero id-cell)}) ∙ suc (svar "n") ≡ᵇ
                                                           suc (plus' (var' "n" {vsuc (vzero id-cell)}) ∙ svar "n"))
                                (∀-elim 𝟙 plus-sucʳ proof-plus-sucʳ (svar "n")) (svar "m")))))

test-plus-comm : (PCResult.goals <$> check-proof ◇ proof-plus-comm plus-comm) ≡ ok []
test-plus-comm = refl


--------------------------------------------------
-- Tests for α-equivalence

α-test-prop1 : bProp ◇
α-test-prop1 = (lam[ "x" ∈ Bool' ] (lam[ "f" ∈ Bool' ⇛ Bool' ] svar "f" ∙ svar "x"))
                     ≡ᵇ (lam[ "b" ∈ Bool' ] (lam[ "g" ∈ Bool' ⇛ Bool' ] svar "g" ∙ svar "b"))

α-test1 : (PCResult.goals <$> check-proof ◇ refl α-test-prop1) ≡ ok []
α-test1 = refl

αβ-test-prop2 : bProp ◇
αβ-test-prop2 = ∀[ 𝟙 ∣ "b" ∈ Bool' ] ((lam[ "x" ∈ Bool' ] (lam[ "f" ∈ Bool' ⇛ Bool' ] svar "f" ∙ svar "x")) ∙ svar "b")
                                       ≡ᵇ (lam[ "g" ∈ Bool' ⇛ Bool' ] svar "g" ∙ svar "b")

αβ-test2 : (PCResult.goals <$> check-proof ◇ (∀-intro[ 𝟙 ∣ "b" ∈ Bool' ] by-normalization) αβ-test-prop2) ≡ ok []
αβ-test2 = refl

α-test-prop3 : bProp ◇
α-test-prop3 = (∀[ 𝟙 ∣ "n" ∈ Nat' ] svar "n" ≡ᵇ svar "n") ⊃ (∀[ 𝟙 ∣ "m" ∈ Nat' ] svar "m" ≡ᵇ svar "m")

α-test3 : (PCResult.goals <$> check-proof ◇ (⊃-intro "reflexivity" (assumption' "reflexivity" {𝟙} {𝟙} id-cell)) α-test-prop3) ≡ ok []
α-test3 = refl

α-test-prop4 : bProp ◇
α-test-prop4 = (∀[ 𝟙 ∣ "n" ∈ Nat' ] (lam[ "m" ∈ Nat' ] svar "n") ≡ᵇ (lam[ "n" ∈ Nat' ] svar "n"))
                 ⊃ (∀[ 𝟙 ∣ "m" ∈ Nat' ] (lam[ "n" ∈ Nat' ] svar "m") ≡ᵇ lam[ "x" ∈ Nat' ] svar "x")

α-test4 : (PCResult.goals <$> check-proof ◇ (⊃-intro "silly assumption" (assumption' "silly assumption" {𝟙} {𝟙} id-cell)) α-test-prop4) ≡ ok []
α-test4 = refl

α-test-prop5 : bProp ◇
α-test-prop5 = ∀[ 𝟙 ∣ "m" ∈ Nat' ] ∀[ 𝟙 ∣ "k" ∈ Nat' ] ∀[ 𝟙 ∣ "x" ∈ Nat' ]
  plus' (plus' (svar "m") ∙ svar "k") ∙ suc (svar "x") ≡ᵇ suc (plus' (plus' (svar "m") ∙ svar "k") ∙ (svar "x"))

α-test-proof5 : Proof ◇
α-test-proof5 =
  ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] (∀-intro[ 𝟙 ∣ "k" ∈ Nat' ]
    ∀-elim 𝟙 plus-sucʳ
             proof-plus-sucʳ
             (plus' (svar "m") ∙ svar "k"))

α-test5 : (PCResult.goals <$> check-proof ◇ α-test-proof5 α-test-prop5) ≡ ok []
α-test5 = refl
