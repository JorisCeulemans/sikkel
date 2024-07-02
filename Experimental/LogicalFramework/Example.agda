--------------------------------------------------
-- Examples of MSTT programs and proofs of their properties
--------------------------------------------------

module Experimental.LogicalFramework.Example where

open import Data.Bool using (Bool)
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

plus-◇ : Tm ◇ (Nat' ⇛ Nat' ⇛ Nat')
plus-◇ = plus

sem-plus : M.Tm M.◇ (M.Nat' M.⇛ M.Nat' M.⇛ M.Nat')
sem-plus = ⟦ plus-◇ ⟧tm

_+_ : ℕ → ℕ → ℕ
_+_ = extract-tm-◇ plus-◇

_ : 1 + 1 ≡ 2
_ = refl


suc' : Tm Γ (Nat' ⇛ Nat')
suc' = lam[ "n" ∈ Nat' ] suc (svar "n")

cong-suc : {Γ : Ctx ★} (m n : Tm Γ Nat') → Proof (Γ ,lock⟨ 𝟙 ⟩) → Proof Γ
cong-suc m n p = trans (suc' ∙¹ m) by-normalization (trans (suc' ∙¹ n) (cong suc' p) by-normalization)


-- ∀ n → plus n 0 = n
plus-zeroʳ : ∀ {Γ} → bProp Γ
plus-zeroʳ = ∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ (svar "n") ∙ zero ≡ᵇ svar "n")

proof-plus-zeroʳ : {Γ : Ctx ★} → Proof Γ
proof-plus-zeroʳ {Γ = Γ} =
  ∀-intro[ 𝟙 ∣ "n" ∈ Nat' ]
    nat-induction "ind-hyp"
      by-normalization
      suc-case
  where
    open ≡ᵇ-Reasoning
    suc-case =
      begin
        plus ∙ suc (svar "n") ∙ zero
      ≡ᵇ⟨ by-normalization ⟩
        suc (plus ∙ svar "n" ∙ zero)
      ≡ᵇ⟨ cong-suc (plus ∙ (svar "n") ∙ zero) (svar "n") (assumption' "ind-hyp" {𝟙} {𝟙} id-cell) ⟩
        suc (svar "n") ∎

test-proof-plus-zeroʳ : IsOk (check-proof ◇ proof-plus-zeroʳ plus-zeroʳ)
test-proof-plus-zeroʳ = _

-- extract-plus-zeroʳ : (n : ℕ) → (n + 0) ≡ n
-- extract-plus-zeroʳ = extract-proof-◇ proof-plus-zeroʳ plus-zeroʳ


-- ∀ m n → plus m (suc n) = suc (plus m n)
plus-sucʳ : bProp Γ
plus-sucʳ = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus ∙ svar "m" ∙ suc (svar "n") ≡ᵇ suc (plus ∙ svar "m" ∙ svar "n")))

proof-plus-sucʳ : {Γ : Ctx ★} → Proof Γ
proof-plus-sucʳ = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp"
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] by-normalization)
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] suc-case)
  where
    open ≡ᵇ-Reasoning
    suc-case =
      begin
        plus ∙ suc (svar "m") ∙ suc (svar "n")
      ≡ᵇ⟨ by-normalization ⟩
        suc (plus ∙ svar "m" ∙ suc (svar "n"))
      ≡ᵇ⟨ cong-suc (plus ∙ svar "m" ∙ suc (svar "n")) (suc (plus ∙ svar "m" ∙ svar "n"))
                   (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ svar "m" ∙ suc (svar "n") ≡ᵇ suc (plus ∙ svar "m" ∙ svar "n"))
                             (assumption' "ind-hyp" {𝟙} {𝟙} id-cell) (svar "n")) ⟩
        suc (suc (plus ∙ svar "m" ∙ svar "n"))
      ≡ᵇ⟨ by-normalization ⟩
        suc (plus ∙ suc (svar "m") ∙ svar "n") ∎

test-plus-sucʳ : IsOk (check-proof ◇ proof-plus-sucʳ plus-sucʳ)
test-plus-sucʳ = _

-- extract-plus-sucʳ : (m n : ℕ) → (m + suc n) ≡ suc (m + n)
-- extract-plus-sucʳ = {!extract-proof-◇ proof-plus-sucʳ plus-sucʳ!}


-- ∀ m n → plus m n = plus n m
plus-comm : bProp Γ
plus-comm = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus ∙ svar "m" ∙ svar "n" ≡ᵇ plus ∙ svar "n" ∙ svar "m"))

proof-plus-comm : {Γ : Ctx ★} → Proof Γ
proof-plus-comm = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp"
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] zero-case)
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] suc-case)
  where
    open ≡ᵇ-Reasoning
    zero-case =
      begin
        plus ∙ zero ∙ svar "n"
      ≡ᵇ⟨ by-normalization ⟩
        svar "n"
      ≡ᵇ⟨ ∀-elim 𝟙 plus-zeroʳ proof-plus-zeroʳ (svar "n") ⟨
        plus ∙ svar "n" ∙ zero ∎

    suc-case =
      begin
        plus ∙ suc (svar "m") ∙ svar "n"
      ≡ᵇ⟨ by-normalization ⟩
        suc (plus ∙ svar "m" ∙ svar "n")
      ≡ᵇ⟨ cong-suc (plus ∙ svar "m" ∙ svar "n") (plus ∙ svar "n" ∙ svar "m")
                   (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ svar "m" ∙ svar "n" ≡ᵇ plus ∙ svar "n" ∙ svar "m")
                             (assumption' "ind-hyp" {𝟙} {𝟙} id-cell)
                             (svar "n")) ⟩
        suc (plus ∙ svar "n" ∙ svar "m")
      ≡ᵇ⟨ ∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ v1 ∙ suc (svar "n") ≡ᵇ suc (plus ∙ v1 ∙ svar "n"))
                   (∀-elim 𝟙 plus-sucʳ proof-plus-sucʳ (svar "n"))
                   (svar "m") ⟨
        plus ∙ svar "n" ∙ suc (svar "m") ∎

test-plus-comm : IsOk (check-proof ◇ proof-plus-comm plus-comm)
test-plus-comm = _

-- extract-plus-comm : (m n : ℕ) → m + n ≡ n + m
-- extract-plus-comm = {!extract-proof-◇ proof-plus-comm plus-comm!}


--------------------------------------------------
-- Tests for α-equivalence

α-test-prop1 : bProp Γ
α-test-prop1 = (lam[ "x" ∈ Bool' ] (lam[ "f" ∈ Bool' ⇛ Bool' ] svar "f" ∙ svar "x"))
                     ≡ᵇ (lam[ "b" ∈ Bool' ] (lam[ "g" ∈ Bool' ⇛ Bool' ] svar "g" ∙ svar "b"))

α-test1 : IsOk (check-proof ◇ refl α-test-prop1)
α-test1 = _

αβ-test-prop2 : bProp Γ
αβ-test-prop2 = ∀[ 𝟙 ∣ "b" ∈ Bool' ] ((lam[ "x" ∈ Bool' ] (lam[ "f" ∈ Bool' ⇛ Bool' ] svar "f" ∙ svar "x")) ∙ svar "b")
                                       ≡ᵇ (lam[ "g" ∈ Bool' ⇛ Bool' ] svar "g" ∙ svar "b")

αβ-test2 : IsOk (check-proof ◇ (∀-intro[ 𝟙 ∣ "b" ∈ Bool' ] by-normalization) αβ-test-prop2)
αβ-test2 = _

α-test-prop3 : bProp Γ
α-test-prop3 = (∀[ 𝟙 ∣ "n" ∈ Nat' ] svar "n" ≡ᵇ svar "n") ⊃ (∀[ 𝟙 ∣ "m" ∈ Nat' ] svar "m" ≡ᵇ svar "m")

α-test3 : IsOk (check-proof ◇ (⊃-intro "reflexivity" (assumption' "reflexivity" {𝟙} {𝟙} id-cell)) α-test-prop3)
α-test3 = _

α-test-prop4 : bProp Γ
α-test-prop4 = (∀[ 𝟙 ∣ "n" ∈ Nat' ] (lam[ "m" ∈ Nat' ] svar "n") ≡ᵇ (lam[ "n" ∈ Nat' ] svar "n"))
                 ⊃ (∀[ 𝟙 ∣ "m" ∈ Nat' ] (lam[ "n" ∈ Nat' ] svar "m") ≡ᵇ lam[ "x" ∈ Nat' ] svar "x")

α-test4 : IsOk (check-proof ◇ (⊃-intro "silly assumption" (assumption' "silly assumption" {𝟙} {𝟙} id-cell)) α-test-prop4)
α-test4 = _

α-test-prop5 : bProp Γ
α-test-prop5 = ∀[ 𝟙 ∣ "m" ∈ Nat' ] ∀[ 𝟙 ∣ "k" ∈ Nat' ] ∀[ 𝟙 ∣ "x" ∈ Nat' ]
  plus ∙ (plus ∙ svar "m" ∙ svar "k") ∙ suc (svar "x") ≡ᵇ suc (plus ∙ (plus ∙ svar "m" ∙ svar "k") ∙ svar "x")

α-test-proof5 : Proof ◇
α-test-proof5 =
  ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] (∀-intro[ 𝟙 ∣ "k" ∈ Nat' ]
    ∀-elim 𝟙 plus-sucʳ
             proof-plus-sucʳ
             (plus ∙ svar "m" ∙ svar "k"))

α-test5 : IsOk (check-proof ◇ α-test-proof5 α-test-prop5)
α-test5 = _


--------------------------------------------------
-- Tests for extraction

extract-test1-prop : bProp {★} ◇
extract-test1-prop =
  ∀[ 𝟙 ∣ "f" ∈ Nat' ⇛ Nat' ⇛ Nat' ] ∀[ 𝟙 ∣ "x" ∈ Bool' ] svar "f" ∙ zero ∙ (suc zero) ≡ᵇ svar "f" ∙ zero ∙ (suc zero)

extract-test1-proof : Proof {★} ◇
extract-test1-proof = ∀-intro[ 𝟙 ∣ "f" ∈ Nat' ⇛ Nat' ⇛ Nat' ] ∀-intro[ 𝟙 ∣ "x" ∈ Bool' ] refl

extract-test1 : (f : ℕ → ℕ → ℕ) (x : Bool) → f 0 1 ≡ f 0 1
extract-test1 = extract-proof-◇ extract-test1-proof extract-test1-prop


id-bool not : Tm Γ (Bool' ⇛ Bool')
id-bool = lam[ "b" ∈ Bool' ] svar "b"
not = lam[ "y" ∈ Bool' ] if (svar "y") false true

xor : Tm Γ (Bool' ⇛ Bool' ⇛ Bool')
xor = lam[ "x" ∈ Bool' ] if (svar "x") (weaken-tm not) (weaken-tm id-bool)

extract-xor : Bool → Bool → Bool
extract-xor = extract-tm-◇ xor

extract-test2-prop : bProp {★} ◇
extract-test2-prop = ∀[ 𝟙 ∣ "b" ∈ Bool' ] weaken-tm xor ∙ svar "b" ∙ svar "b" ≡ᵇ false

-- extract-test2 : extract-bprop extract-test2-prop _
--                   ≡
--                 ((b : Bool) → extract-tm-◇ xor b b ≡ Bool.false)
-- extract-test2 = {!refl!}
