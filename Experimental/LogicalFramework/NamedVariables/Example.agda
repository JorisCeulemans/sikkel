--------------------------------------------------
-- Examples of STT programs and proofs of their properties
--------------------------------------------------

module Experimental.LogicalFramework.NamedVariables.Example where

open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Experimental.LogicalFramework.NamedVariables.STT
open import Experimental.LogicalFramework.NamedVariables.Formula
open import Experimental.LogicalFramework.NamedVariables.Derivation
open import Experimental.LogicalFramework.NamedVariables.BetaReduction
open import Extraction

open import Model.BaseCategory
import Model.CwF-Structure as M
import Model.Type.Discrete as M
import Model.Type.Function as M
import Experimental.DependentTypes.Model.Function as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.ClosedTypes as M

private variable
  Γ : CtxExpr
  T : TyExpr


--------------------------------------------------
-- Proving some properties of natural number addition

id : TmExpr Γ (T ⇛ T)
id = lam[ "x" ∈ _ ] var "x"

plus : TmExpr Γ (Nat' ⇛ Nat' ⇛ Nat')
plus = nat-elim id (lam[ "f" ∈ Nat' ⇛ Nat' ] (lam[ "n" ∈ Nat' ] (suc ∙ (var "f" ∙ var "n"))))

sem-plus : M.Tm (M.◇ {★}) ((M.Nat' M.⇛ M.Nat' M.⇛ M.Nat') M.[ _ ])
sem-plus = ⟦ plus {◇} ⟧tm

{-
_+_ : ℕ → ℕ → ℕ
_+_ = extract-term ⟦ plus {◇} ⟧tm

_ : 16 + 9 ≡ 25
_ = refl
-}

-- ∀ n → plus n 0 = n
plus-zeroʳ : Formula Γ
plus-zeroʳ = ∀[ "n" ∈ Nat' ] (plus ∙ var "n" ∙ zero ≡ᶠ var "n")

proof-plus-zeroʳ : {Ξ : ProofCtx} → Ξ ⊢ plus-zeroʳ
proof-plus-zeroʳ =
  ∀-intro (nat-induction "ind-hyp"
            (trans (fun-cong nat-elim-β-zero zero) fun-β)
            (trans (fun-cong (trans nat-elim-β-suc fun-β) zero) (trans fun-β (cong suc (assumption "ind-hyp")))))

proof-plus-zeroʳ-with-β : ∀ {Ξ} → Ξ ⊢ plus-zeroʳ
proof-plus-zeroʳ-with-β =
  ∀-intro (nat-induction "ind-hyp"
    (reduce 2)
    (with-reduce-left 3 (cong suc (assumption "ind-hyp"))))

⟦proof-plus-zeroʳ⟧ : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _) M.[ _ ])
⟦proof-plus-zeroʳ⟧ = ⟦ proof-plus-zeroʳ {Ξ = []} ⟧der

-- ∀ m n → plus m (suc n) = suc (plus m n)
plus-sucʳ : Formula Γ
plus-sucʳ = ∀[ "m" ∈ Nat' ] (∀[ "n" ∈ Nat' ] (
  plus ∙ var "m" ∙ (suc ∙ var "n") ≡ᶠ suc ∙ (plus ∙ var "m" ∙ var "n")))

proof-plus-sucʳ : {Ξ : ProofCtx} → Ξ ⊢ plus-sucʳ
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

-- ∀ m n → plus m n = plus n m
plus-comm : Formula Γ
plus-comm = ∀[ "m" ∈ Nat' ] (∀[ "n" ∈ Nat' ] (
  plus ∙ var "m" ∙ var "n" ≡ᶠ plus ∙ var "n" ∙ var "m"))

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
