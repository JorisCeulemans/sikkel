module Experimental.LogicalFramework.NamedVariables.STT.Interpretation.Nameless where

open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M

open import Experimental.ClosedTypes as M

open import Experimental.LogicalFramework.NamedVariables.STT.Syntax.Nameless
open import Experimental.LogicalFramework.NamedVariables.STT.AlphaEquivalence

private variable
  Γ : CtxExpr
  T : TyExpr


⟦_⟧ty : TyExpr → ClosedTy ★
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty

⟦_⟧ctx-nmls : CtxExpr → Ctx ★
⟦ ◇ ⟧ctx-nmls = M.◇
⟦ Γ ,, _ ∈ T ⟧ctx-nmls = ⟦ Γ ⟧ctx-nmls ,,ₛ ⟦ T ⟧ty

⟦_,_⟧var-nmls : (v : Var _ Γ) → lookup-var v ≡ T → SimpleTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦ vzero  , refl ⟧var-nmls = sξ
⟦ vsuc v , e    ⟧var-nmls = ⟦ v , e ⟧var-nmls [ M.π ]s

⟦_⟧tm-nmls : TmExpr Γ T → SimpleTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦ var' _ {v} {e} ⟧tm-nmls = ⟦ v , e ⟧var-nmls
⟦ lam[ _ ∈ _ ] t ⟧tm-nmls = sλ[ _ ] ⟦ t ⟧tm-nmls
⟦ f ∙ t ⟧tm-nmls = ⟦ f ⟧tm-nmls ∙ₛ ⟦ t ⟧tm-nmls
⟦ zero ⟧tm-nmls = szero
⟦ suc ⟧tm-nmls = ssuc
⟦ nat-elim a f ⟧tm-nmls = snat-elim ⟦ a ⟧tm-nmls ⟦ f ⟧tm-nmls
⟦ true ⟧tm-nmls = strue
⟦ false ⟧tm-nmls = sfalse
⟦ if b t f ⟧tm-nmls = sif ⟦ b ⟧tm-nmls ⟦ t ⟧tm-nmls ⟦ f ⟧tm-nmls
⟦ pair t s ⟧tm-nmls = spair ⟦ t ⟧tm-nmls ⟦ s ⟧tm-nmls
⟦ fst p ⟧tm-nmls = sfst ⟦ p ⟧tm-nmls
⟦ snd p ⟧tm-nmls = ssnd ⟦ p ⟧tm-nmls
