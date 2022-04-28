--------------------------------------------------
-- Example in which we (try to) prove that ∀ n . n + 0 = n
--------------------------------------------------

module Experimental.ProgramLogic.Example where

open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Experimental.ProgramLogic.STT
open import Experimental.ProgramLogic.Formula
open import Extraction

private variable
  Γ : CtxExpr
  T : TyExpr


id : TmExpr Γ (T ⇛ T)
id = lam (var vzero)

plus : TmExpr Γ (Nat' ⇛ Nat' ⇛ Nat')
plus = nat-elim id (lam (lam (suc ∙ (var (vsuc vzero) ∙ var vzero))))

_+_ : ℕ → ℕ → ℕ
_+_ = extract-term ⟦ plus {◇} ⟧tm

_ : 16 + 9 ≡ 25
_ = refl

plus-zeroʳ : Formula Γ
plus-zeroʳ = ∀[ Nat' ] (plus ∙ var vzero ∙ lit 0 ≡ᶠ var vzero)

module SplitEnvironment where
  open import Experimental.ProgramLogic.Derivation.SplitEnvironment
  
  proof-plus-zeroʳ : Γ ∣ [] ⊢ plus-zeroʳ
  proof-plus-zeroʳ =
    ∀-intro (nat-induction (trans (fun-cong nat-elim-β-zero (lit 0)) fun-β)
                           (trans (fun-cong (trans nat-elim-β-suc fun-β) _) (trans fun-β (cong suc (assumption azero)))))

module OneEnvironment where
  open import Experimental.ProgramLogic.Derivation.OneEnvironment

  proof-plus-zeroʳ : [] ⊢ plus-zeroʳ
  proof-plus-zeroʳ =
    ∀-intro (nat-induction (trans (fun-cong nat-elim-β-zero (lit 0)) fun-β)
                           (trans (fun-cong (trans nat-elim-β-suc fun-β) (lit 0)) (trans fun-β (cong suc (assumption azero)))))
