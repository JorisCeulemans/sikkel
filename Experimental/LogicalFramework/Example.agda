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
import Model.Type.Discrete as M
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

{-
proof-plus-zeroʳ : {Ξ : ProofCtx ★} → Proof Ξ
proof-plus-zeroʳ = ∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] nat-induction "ind-hyp" (plus ∙ svar "n" ∙ zero ≡ᶠ svar "n")
  (trans (id ∙ zero) (fun-cong nat-elim-β-zero zero) fun-β)
  (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ var' "n" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell))) ∙ zero)
         (fun-cong (trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n")))) ∙ (plus ∙ svar "n"))
                          nat-elim-β-suc
                          fun-β) zero)
         (trans (suc ∙ (plus ∙ svar "n" ∙ zero))
                fun-β
                (cong suc (assumption' "ind-hyp" azero id-cell))))
-}

proof-plus-zeroʳ : {Ξ : ProofCtx ★} → Proof Ξ
proof-plus-zeroʳ = ∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] nat-induction "ind-hyp" (plus ∙ var' "n" {vzero} id-cell ∙ zero ≡ᶠ var' "n" {vzero} id-cell)
  (trans (id ∙ zero) (fun-cong nat-elim-β-zero zero) fun-β)
  (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ var' "n" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell))) ∙ zero)
         (fun-cong (trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (var' "f" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell)))) ∙ (plus ∙ var' "n" {vzero} id-cell))
                          nat-elim-β-suc
                          fun-β) zero)
         (trans (suc ∙ (plus ∙ var' "n" {vzero} id-cell ∙ zero))
                fun-β
                (cong suc (assumption' "ind-hyp" azero id-cell))))

test-plus-zeroʳ : {Ξ : ProofCtx ★} → check-proof Ξ proof-plus-zeroʳ plus-zeroʳ ≡ ok _
test-plus-zeroʳ = refl

{-
postulate
  fun-cong : {Ξ : ProofCtx m} {T S : Ty m} {f g : Tm (to-ctx Ξ) (T ⇛ S)} →
             (Ξ ⊢ f ≡ᶠ g) →
             (t : Tm (to-ctx Ξ) T) →
             (Ξ ⊢ f ∙ t ≡ᶠ g ∙ t)
  cong : {Ξ : ProofCtx m} {T S : Ty m} (f : Tm (to-ctx Ξ) (T ⇛ S)) {t1 t2 : Tm (to-ctx Ξ) T} →
         (Ξ ⊢ t1 ≡ᶠ t2) →
         (Ξ ⊢ f ∙ t1 ≡ᶠ f ∙ t2)

proof-plus-zeroʳ : {Ξ : ProofCtx ★} → Ξ ⊢ plus-zeroʳ
proof-plus-zeroʳ =
  ∀-intro (nat-induction "ind-hyp"
    (trans (fun-cong nat-elim-β-zero zero) fun-β)
    (trans (fun-cong (trans nat-elim-β-suc fun-β) zero) (trans fun-β (cong suc (assumption "ind-hyp" id-cell)))))

{-
proof-plus-zeroʳ-with-β : ∀ {Ξ} → Ξ ⊢ plus-zeroʳ
proof-plus-zeroʳ-with-β =
  ∀-intro (nat-induction "ind-hyp"
    (reduce 2)
    (with-reduce-left 3 (cong suc (assumption "ind-hyp"))))

⟦proof-plus-zeroʳ⟧ : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _) M.[ _ ])
⟦proof-plus-zeroʳ⟧ = ⟦ proof-plus-zeroʳ {Ξ = []} ⟧der
-}
-}

-- ∀ m n → plus m (suc n) = suc (plus m n)
plus-sucʳ : Formula Γ
plus-sucʳ = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus ∙ svar "m" ∙ (suc ∙ svar "n") ≡ᶠ suc ∙ (plus ∙ svar "m" ∙ svar "n")))

{-
proof-plus-sucʳ : {Ξ : ProofCtx ★} → Proof Ξ
proof-plus-sucʳ = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp" (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ svar "m" ∙ (suc ∙ svar "n") ≡ᶠ suc ∙ (plus ∙ svar "m" ∙ svar "n"))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans (id ∙ (suc ∙ svar "n")) (fun-cong nat-elim-β-zero (suc ∙ svar "n")) (trans (suc ∙ svar "n") fun-β (sym (cong suc (trans (id ∙ svar "n") (fun-cong nat-elim-β-zero (svar "n")) fun-β)))))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n")))) ∙ (plus ∙ svar "m") ∙ (suc ∙ svar "n"))
                                   (fun-cong nat-elim-β-suc (suc ∙ svar "n"))
                                   (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ svar "m" ∙ svar "n"))) ∙ (suc ∙ svar "n"))
                                          (fun-cong fun-β (suc ∙ svar "n"))
                                          (trans (suc ∙ (plus ∙ svar "m" ∙ (suc ∙ svar "n")))
                                                 fun-β
                                                 (cong suc (trans (suc ∙ (plus ∙ svar "m" ∙ svar "n"))
                                                                  (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ svar "m" ∙ (suc ∙ svar "n") ≡ᶠ suc ∙ (plus ∙ svar "m" ∙ svar "n")) (assumption' "ind-hyp" (skip-var azero) id-cell) (svar "n"))
                                                                  (sym (trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (svar "f" ∙ svar "n")))) ∙ (plus ∙ svar "m") ∙ svar "n")
                                                                              (fun-cong nat-elim-β-suc (svar "n"))
                                                                              (trans ((lam[ "n" ∈ Nat' ] suc ∙ (plus ∙ svar "m" ∙ svar "n")) ∙ svar "n")
                                                                                     (fun-cong fun-β (svar "n"))
                                                                                     fun-β))))))))
-}

proof-plus-sucʳ : {Ξ : ProofCtx ★} → Proof Ξ
proof-plus-sucʳ = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp" (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ var' "m" {vsuc vzero} id-cell ∙ (suc ∙ var' "n" {vzero} id-cell) ≡ᶠ suc ∙ (plus ∙ var' "m" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans (id ∙ (suc ∙ var' "n" {vzero} id-cell)) (fun-cong nat-elim-β-zero (suc ∙ var' "n" {vzero} id-cell)) (trans (suc ∙ var' "n" {vzero} id-cell) fun-β (sym (cong suc (trans (id ∙ var' "n" {vzero} id-cell) (fun-cong nat-elim-β-zero (var' "n" {vzero} id-cell)) fun-β)))))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (var' "f" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell)))) ∙ (plus ∙ var' "m" {vsuc vzero} id-cell) ∙ (suc ∙ var' "n" {vzero} id-cell))
                                   (fun-cong nat-elim-β-suc (suc ∙ var' "n" {vzero} id-cell))
                                   (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ var' "m" {vsuc (vsuc vzero)} id-cell ∙ var' "n" {vzero} id-cell))) ∙ (suc ∙ var' "n" {vzero} id-cell))
                                          (fun-cong fun-β (suc ∙ var' "n" {vzero} id-cell))
                                          (trans (suc ∙ (plus ∙ var' "m" {vsuc vzero} id-cell ∙ (suc ∙ var' "n" {vzero} id-cell)))
                                                 fun-β
                                                 (cong suc (trans (suc ∙ (plus ∙ var' "m" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell))
                                                                  (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] plus ∙ var' "m" {vsuc (vsuc vzero)} id-cell ∙ (suc ∙ var' "n" {vzero} id-cell) ≡ᶠ suc ∙ (plus ∙ var' "m" {vsuc (vsuc vzero)} id-cell ∙ var' "n" {vzero} id-cell)) (assumption' "ind-hyp" (skip-var azero) id-cell) (var' "n" {skip-lock 𝟙 vzero} id-cell))
                                                                  (sym (trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (var' "f" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell)))) ∙ (plus ∙ var' "m" {vsuc vzero} id-cell) ∙ var' "n" {vzero} id-cell)
                                                                              (fun-cong nat-elim-β-suc (var' "n" {vzero} id-cell))
                                                                              (trans ((lam[ "n" ∈ Nat' ] suc ∙ (plus ∙ var' "m" {vsuc (vsuc vzero)} id-cell ∙ var' "n" {vzero} id-cell)) ∙ var' "n" {vzero} id-cell)
                                                                                     (fun-cong fun-β (var' "n" {vzero} id-cell))
                                                                                     fun-β))))))))

test-plus-sucʳ : {Ξ : ProofCtx ★} → check-proof Ξ proof-plus-sucʳ plus-sucʳ ≡ ok _
test-plus-sucʳ = refl


{-
proof-plus-sucʳ : {Ξ : ProofCtx ★} → Ξ ⊢ plus-sucʳ
proof-plus-sucʳ = ∀-intro (nat-induction "ind-hyp"
  (∀-intro (trans (fun-cong nat-elim-β-zero _) (trans fun-β (sym (cong suc (trans (fun-cong nat-elim-β-zero _) fun-β))))))
  (∀-intro (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) (trans fun-β
    (cong suc (trans (∀-elim (assumption "ind-hyp" id-cell) (svar "n"))
                     (sym (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) fun-β))))))))))

proof-plus-sucʳ = ∀-intro (nat-induction "ind-hyp"
  (∀-intro (trans (fun-cong nat-elim-β-zero _) (trans fun-β (sym (cong suc (trans (fun-cong nat-elim-β-zero _) fun-β))))))
  (∀-intro (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) (trans fun-β (
    cong suc (trans (∀-elim (assumption "ind-hyp") (var "n"))
                    (sym (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) fun-β))))))))))

proof-plus-sucʳ-with-β : ∀ {Ξ} → Ξ ⊢ plus-sucʳ
proof-plus-sucʳ-with-β = ∀-intro (nat-induction "ind-hyp"
  (∀-intro (with-reduce 2 refl))
  (∀-intro (with-reduce 3 (cong suc (∀-elim (assumption "ind-hyp") (var "n"))))))

⟦proof-plus-sucʳ⟧ : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _)) M.[ _ ])
⟦proof-plus-sucʳ⟧ = ⟦ proof-plus-sucʳ {Ξ = []} ⟧der
-}

-- ∀ m n → plus m n = plus n m
plus-comm : Formula Γ
plus-comm = ∀[ 𝟙 ∣ "m" ∈ Nat' ] (∀[ 𝟙 ∣ "n" ∈ Nat' ] (
  plus ∙ svar "m" ∙ svar "n" ≡ᶠ plus ∙ svar "n" ∙ svar "m"))

proof-plus-comm : {Ξ : ProofCtx ★} → Proof Ξ
proof-plus-comm = ∀-intro[ 𝟙 ∣ "m" ∈ Nat' ] nat-induction "ind-hyp" (∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ var' "m" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell ≡ᶠ plus ∙ var' "n" {vzero} id-cell ∙ var' "m" {vsuc vzero} id-cell))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans (id ∙ var' "n" {vzero} id-cell) (fun-cong nat-elim-β-zero (var' "n" {vzero} id-cell)) (trans (var' "n" {vzero} id-cell) fun-β (sym (∀-elim 𝟙 plus-zeroʳ proof-plus-zeroʳ (var' "n" {skip-lock 𝟙 vzero} id-cell)))))
  (∀-intro[ 𝟙 ∣ "n" ∈ Nat' ] trans ((lam[ "f" ∈ Nat' ⇛ Nat' ] lam[ "n" ∈ Nat' ] suc ∙ (var' "f" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell)) ∙ (plus ∙ var' "m" {vsuc vzero} id-cell) ∙ var' "n" {vzero} id-cell)
                                   (fun-cong nat-elim-β-suc (var' "n" {vzero} id-cell))
                                   (trans ((lam[ "n" ∈ Nat' ] (suc ∙ (plus ∙ var' "m" {vsuc (vsuc vzero)} id-cell ∙ var' "n" {vzero} id-cell))) ∙ var' "n" {vzero} id-cell)
                                          (fun-cong fun-β (var' "n" {vzero} id-cell))
                                          (trans (suc ∙ (plus ∙ var' "m" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell)) fun-β
                                            (trans (suc ∙ (plus ∙ var' "n" {vzero} id-cell ∙ var' "m" {vsuc vzero} id-cell))
                                                   (cong suc (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ var' "m" {vsuc (vsuc vzero)} id-cell ∙ var' "n" {vzero} id-cell ≡ᶠ plus ∙ var' "n" {vzero} id-cell ∙ var' "m" {vsuc (vsuc vzero)} id-cell)) (assumption' "ind-hyp" (skip-var azero) id-cell) (var' "n" {skip-lock 𝟙 vzero} id-cell)))
                                                   (sym (∀-elim 𝟙 (∀[ 𝟙 ∣ "n" ∈ Nat' ] (plus ∙ var' "n" {vsuc vzero} id-cell ∙ (suc ∙ var' "n" {vzero} id-cell) ≡ᶠ suc ∙ (plus ∙ var' "n" {vsuc vzero} id-cell ∙ var' "n" {vzero} id-cell))) (∀-elim 𝟙 plus-sucʳ proof-plus-sucʳ (var' "n" {skip-lock 𝟙 vzero} id-cell)) (var' "m" {skip-lock 𝟙 (vsuc vzero)} id-cell)))))))

test-plus-comm : check-proof [] proof-plus-comm plus-comm ≡ ok _
test-plus-comm = refl

{-
proof-plus-comm : {Ξ : ProofCtx} → Ξ ⊢ plus-comm
proof-plus-comm = ∀-intro (nat-induction "ind-hyp"
  (∀-intro (trans (fun-cong nat-elim-β-zero _) (trans fun-β (sym (∀-elim proof-plus-zeroʳ (var "n"))))))
  (∀-intro (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) (trans fun-β (trans
       (cong suc (∀-elim (assumption "ind-hyp") (var "n")))
       (sym (∀-elim (∀-elim proof-plus-sucʳ (var "n")) (var "m")))))))))

proof-plus-comm-with-β : ∀ {Ξ} → Ξ ⊢ plus-comm
proof-plus-comm-with-β = ∀-intro (nat-induction "ind-hyp"
  (∀-intro (with-reduce-left 2 (sym (∀-elim proof-plus-zeroʳ (var "n")))))
  (∀-intro (with-reduce-left 3 (trans
    (cong suc (∀-elim (assumption "ind-hyp") (var "n")))
    (sym (∀-elim (∀-elim proof-plus-sucʳ (var "n")) (var "m")))))))

⟦plus-comm-proof⟧ : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _)) M.[ _ ])
⟦plus-comm-proof⟧ = ⟦ proof-plus-comm {Ξ = []} ⟧der


--------------------------------------------------
-- Tests for α-equivalence

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
