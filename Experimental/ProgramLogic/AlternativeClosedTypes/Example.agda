--------------------------------------------------
-- Example in which we (try to) prove that ∀ n . n + 0 = n
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

plus-zeroʳ : Formula Γ
plus-zeroʳ = ∀[ Nat' ] (plus ∙ var vzero ∙ lit 0 ≡ᶠ var vzero)

proof-plus-zeroʳ : [] ⊢ plus-zeroʳ
proof-plus-zeroʳ =
  ∀-intro (nat-induction (trans (fun-cong nat-elim-β-zero (lit 0)) fun-β)
                         (trans (fun-cong (trans nat-elim-β-suc fun-β) (lit 0)) (trans fun-β (cong suc (assumption azero)))))

sem-proof : M.Tm (M.◇ {★}) (M.Pi (M.Nat' M.[ _ ]) (M.Id _ _) M.[ _ ])
sem-proof = ⟦ proof-plus-zeroʳ ⟧der
