--------------------------------------------------
-- Example in which we (try to) prove that ∀ n . n + 0 = n
--------------------------------------------------

module Experimental.ProgramLogic.Example where

open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality

open import Experimental.ProgramLogic.STT
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
