--------------------------------------------------
-- Examples in which we prove some properties of
--  addition of natural numbers
--------------------------------------------------

module Experimental.ProgramLogic.AlternativeClosedTypes.Example where

open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Experimental.ProgramLogic.AlternativeClosedTypes.STT
open import Experimental.ProgramLogic.AlternativeClosedTypes.Formula
open import Experimental.ProgramLogic.AlternativeClosedTypes.Derivation
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


id : TmExpr Γ (T ⇛ T)
id = lam (var vzero)

plus : TmExpr Γ (Nat' ⇛ Nat' ⇛ Nat')
plus = nat-elim id (lam (lam (suc ∙ (var (vsuc vzero) ∙ var vzero))))

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
plus-zeroʳ = ∀[ Nat' ] (plus ∙ var vzero ∙ zero ≡ᶠ var vzero)

proof-plus-zeroʳ : {Ξ : Env} → Ξ ⊢ plus-zeroʳ
proof-plus-zeroʳ =
  ∀-intro (nat-induction (trans (fun-cong nat-elim-β-zero zero) fun-β)
                         (trans (fun-cong (trans nat-elim-β-suc fun-β) zero) (trans fun-β (cong suc (assumption azero)))))

sem-proof : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _) M.[ _ ])
sem-proof = ⟦ proof-plus-zeroʳ {Ξ = []} ⟧der

-- ∀ m n → plus m (suc n) = suc (plus m n)
plus-sucʳ : Formula Γ
plus-sucʳ = ∀[ Nat' ] (∀[ Nat' ] (plus ∙ var (vsuc vzero) ∙ (suc ∙ var vzero) ≡ᶠ suc ∙ (plus ∙ var (vsuc vzero) ∙ var vzero)))

proof-plus-sucʳ : {Ξ : Env} → Ξ ⊢ plus-sucʳ
proof-plus-sucʳ = ∀-intro (nat-induction
  (∀-intro (trans (fun-cong nat-elim-β-zero _) (trans fun-β (sym (cong suc (trans (fun-cong nat-elim-β-zero _) fun-β))))))
  (∀-intro (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) (trans fun-β
    (cong suc (trans (∀-elim (assumption (skip-var azero)) (var vzero))
                     (sym (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) fun-β))))))))))

⟦proof-plus-sucʳ⟧ : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _)) M.[ _ ])
⟦proof-plus-sucʳ⟧ = ⟦ proof-plus-sucʳ {Ξ = []} ⟧der

-- ∀ m n → plus m n = plus n m
plus-comm : Formula Γ
plus-comm = ∀[ Nat' ] (∀[ Nat' ] (plus ∙ var (vsuc vzero) ∙ var vzero ≡ᶠ (plus ∙ var vzero ∙ var (vsuc vzero))))

proof-plus-comm : {Ξ : Env} → Ξ ⊢ plus-comm
proof-plus-comm = ∀-intro (nat-induction
  (∀-intro (trans (fun-cong nat-elim-β-zero _) (trans fun-β (sym (∀-elim proof-plus-zeroʳ (var vzero))))))
  (∀-intro (trans (fun-cong nat-elim-β-suc _) (trans (fun-cong fun-β _) (trans fun-β (trans
       (cong suc (∀-elim (assumption (skip-var azero)) (var vzero)))
       (sym (∀-elim (∀-elim proof-plus-sucʳ (var vzero)) (var (vsuc vzero))))))))))

⟦plus-comm-proof⟧ : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _)) M.[ _ ])
⟦plus-comm-proof⟧ = ⟦ proof-plus-comm {Ξ = []} ⟧der
