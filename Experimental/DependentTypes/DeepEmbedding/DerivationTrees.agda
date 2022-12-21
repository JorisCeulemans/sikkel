module Experimental.DependentTypes.DeepEmbedding.DerivationTrees where

open import Data.Nat
open import Data.Product
open import Function using (_∘_)

open import Experimental.DependentTypes.DeepEmbedding.Syntax.ForDerivations

private variable
  Γ Δ Θ : CtxExpr
  T S A : TyExpr
  t s f b p : TmExpr
  τ σ : SubstExpr


infix 3 _⊢var_∈_
data _⊢var_∈_ : CtxExpr → ℕ → TyExpr → Set where
  var-zero : Γ ,, A ⊢var 0 ∈ A [ π ]
  var-suc : ∀ {x} → Γ ⊢var x ∈ T → Γ ,, A ⊢var suc x ∈ T [ π ]

infix 3 _⊢ctx _⊢_⇒_ _⊢ty_ _⊢_∈_
data _⊢ctx : CtxExpr → Set
data _⊢_⇒_ : CtxExpr → SubstExpr → CtxExpr → Set
data _⊢ty_ : CtxExpr → TyExpr → Set
data _⊢_∈_ : CtxExpr → TmExpr → TyExpr → Set

data _⊢ctx where
  d-◇ : ◇ ⊢ctx
  d-,, : Γ ⊢ctx → Γ ⊢ty T → Γ ,, T ⊢ctx

data _⊢_⇒_ where
  d-id-subst : Γ ⊢ctx → Γ ⊢ id-subst ⇒ Γ
  d-⊚ : (Γ ⊢ τ ⇒ Θ) → (Δ ⊢ σ ⇒ Γ) → (Δ ⊢ τ ⊚ σ ⇒ Θ)
  d-ε : Γ ⊢ctx → Γ ⊢ ε ⇒ ◇
  d-π : Γ ⊢ty T → Γ ,, T ⊢ π ⇒ Γ
  d-,s : Γ ⊢ σ ⇒ Δ → Γ ⊢ t ∈ T [ σ ] → Γ ⊢ σ ,s t ⇒ Δ ,, T

data _⊢ty_ where
  d-Nat : Γ ⊢ctx → Γ ⊢ty Nat
  d-Bool : Γ ⊢ctx → Γ ⊢ty Bool
  d-⇛ : Γ ⊢ty T → Γ ⊢ty S → Γ ⊢ty T ⇛ S
  d-⊠ : Γ ⊢ty T → Γ ⊢ty S → Γ ⊢ty T ⊠ S
  d-Id : Γ ⊢ctx → Γ ⊢ t ∈ T → Γ ⊢ s ∈ T → Γ ⊢ty Id t s
  d-ty-subst : Γ ⊢ty T → Δ ⊢ σ ⇒ Γ → Δ ⊢ty T [ σ ]

data _⊢_∈_ where
  d-var : Γ ⊢ty T → ∀ {x} → Γ ⊢var x ∈ T → Γ ⊢ var x ∈ T
  d-lam : Γ ,, A ⊢ t ∈ T [ π ] → Γ ⊢ lam A t ∈ A ⇛ T
  d-app : Γ ⊢ f ∈ T ⇛ S → Γ ⊢ t ∈ T → Γ ⊢ f ∙ t ∈ S
  d-lit : ∀ {n} → Γ ⊢ctx → Γ ⊢ lit n ∈ Nat
  d-suc : Γ ⊢ctx → Γ ⊢ suc ∈ Nat ⇛ Nat
  d-plus : Γ ⊢ctx → Γ ⊢ plus ∈ Nat ⇛ Nat ⇛ Nat
  d-true : Γ ⊢ctx → Γ ⊢ true ∈ Bool
  d-false : Γ ⊢ctx → Γ ⊢ false ∈ Bool
  d-if : Γ ⊢ b ∈ Bool → Γ ⊢ t ∈ T → Γ ⊢ f ∈ T → Γ ⊢ if b t f ∈ T
  d-pair : Γ ⊢ t ∈ T → Γ ⊢ s ∈ S → Γ ⊢ pair t s ∈ T ⊠ S
  d-fst : Γ ⊢ p ∈ T ⊠ S → Γ ⊢ fst p ∈ T
  d-snd : Γ ⊢ p ∈ T ⊠ S → Γ ⊢ snd p ∈ S
  d-refl : Γ ⊢ t ∈ T → Γ ⊢ refl t ∈ Id t t
  d-tm-subst : Γ ⊢ t ∈ T → Δ ⊢ σ ⇒ Γ → Δ ⊢ t [ σ ] ∈ T [ σ ]

d-,,-inverse : Γ ,, A ⊢ctx → Γ ⊢ctx × Γ ⊢ty A
d-,,-inverse (d-,, dΓ dA) = dΓ , dA

d-⇛-inverse : Γ ⊢ty T ⇛ S → Γ ⊢ty T × Γ ⊢ty S
d-⇛-inverse (d-⇛ dT dS) = dT , dS

d-⊠-inverse : Γ ⊢ty T ⊠ S → Γ ⊢ty T × Γ ⊢ty S
d-⊠-inverse (d-⊠ dT dS) = dT , dS

valid-subst-to-ctx : Γ ⊢ σ ⇒ Δ → Γ ⊢ctx
valid-ty-to-ctx : Γ ⊢ty T → Γ ⊢ctx
valid-tm-to-ctx : Γ ⊢ t ∈ T → Γ ⊢ctx
valid-tm-to-ty : Γ ⊢ t ∈ T → Γ ⊢ty T

valid-subst-to-ctx (d-id-subst dΓ) = dΓ
valid-subst-to-ctx (d-⊚ dσ dτ) = valid-subst-to-ctx dτ
valid-subst-to-ctx (d-ε dΓ) = dΓ
valid-subst-to-ctx (d-π dT) = d-,, (valid-ty-to-ctx dT) dT
valid-subst-to-ctx (d-,s dσ _) = valid-subst-to-ctx dσ

valid-ty-to-ctx (d-Nat dΓ) = dΓ
valid-ty-to-ctx (d-Bool dΓ) = dΓ
valid-ty-to-ctx (d-⇛ dT dS) = valid-ty-to-ctx dT
valid-ty-to-ctx (d-⊠ dT dS) = valid-ty-to-ctx dT
valid-ty-to-ctx (d-Id dΓ dt ds) = dΓ
valid-ty-to-ctx (d-ty-subst dT dσ) = valid-subst-to-ctx dσ

valid-tm-to-ctx = valid-ty-to-ctx ∘ valid-tm-to-ty

valid-tm-to-ty (d-var dT dv) = dT
valid-tm-to-ty (d-lam dt) = d-⇛ (proj₂ (d-,,-inverse (valid-tm-to-ctx dt))) {!!}
  -- Somehow, we need to prove that if T [ σ ] is well-formed, then T is well-formed.
  --   But the way substitutions are now defined in the syntax, we don't even know in
  --   which context we need to verify this. Maybe substitutions should be indexed by contexts?
  -- Andreas: The derivation via d-ty-subst knows the target context of the substitution.
  --   Moreover, it should be provable that if the substitution is π, then this target must be the "cotail" of the source.
  -- Dominique: Couldn't d-lam additionally contain a validity proof of T [ π ] that you could then recurse on here?
valid-tm-to-ty (d-app df dt) = proj₂ (d-⇛-inverse (valid-tm-to-ty df))
valid-tm-to-ty (d-lit dΓ) = d-Nat dΓ
valid-tm-to-ty (d-suc dΓ) = d-⇛ (d-Nat dΓ) (d-Nat dΓ)
valid-tm-to-ty (d-plus dΓ) = d-⇛ (d-Nat dΓ) (d-⇛ (d-Nat dΓ) (d-Nat dΓ))
valid-tm-to-ty (d-true dΓ) = d-Bool dΓ
valid-tm-to-ty (d-false dΓ) = d-Bool dΓ
valid-tm-to-ty (d-if db dt df) = valid-tm-to-ty dt
valid-tm-to-ty (d-pair dt ds) = d-⊠ (valid-tm-to-ty dt) (valid-tm-to-ty ds)
valid-tm-to-ty (d-fst dp) = proj₁ (d-⊠-inverse (valid-tm-to-ty dp))
valid-tm-to-ty (d-snd dp) = proj₂ (d-⊠-inverse (valid-tm-to-ty dp))
valid-tm-to-ty (d-refl dt) = d-Id (valid-tm-to-ctx dt) dt dt
valid-tm-to-ty (d-tm-subst dt dσ) = d-ty-subst (valid-tm-to-ty dt) dσ

{-
-- Definition needed because first the termination checker was not happy with the valid-ty-to-ctx
--   case for d-Id. However not defining valid-tm-to-ctx as valid-ty-to-ctx ∘ valid-tm-to-ctx
--   gives trouble for implementing the interpretation. Now solved to add extra (redundant?) requirement
--   about context in inference rule for identity types.
-- Andreas: There was redundancy anyway because well-formedness of Γ could be deduced from well-typedness of either s or t.
valid-tm-to-ctx (d-var dT dv) = valid-ty-to-ctx dT
valid-tm-to-ctx (d-lam dt) = proj₁ (d-,,-inverse (valid-tm-to-ctx dt))
valid-tm-to-ctx (d-app df dt) = valid-tm-to-ctx df
valid-tm-to-ctx (d-lit dΓ) = dΓ
valid-tm-to-ctx (d-suc dΓ) = dΓ
valid-tm-to-ctx (d-plus dΓ) = dΓ
valid-tm-to-ctx (d-true dΓ) = dΓ
valid-tm-to-ctx (d-false dΓ) = dΓ
valid-tm-to-ctx (d-if db dt df) = valid-tm-to-ctx db
valid-tm-to-ctx (d-pair dt ds) = valid-tm-to-ctx dt
valid-tm-to-ctx (d-fst dp) = valid-tm-to-ctx dp
valid-tm-to-ctx (d-snd dp) = valid-tm-to-ctx dp
valid-tm-to-ctx (d-refl dt) = valid-tm-to-ctx dt
valid-tm-to-ctx (d-tm-subst dt dσ) = valid-subst-to-ctx dσ
-}

open import Model.CwF-Structure as M
open import Model.BaseCategory
open import Model.Type.Constant as M
open import Model.Type.Function as M
open import Model.Type.Product as M

import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

module ComputeContextsTypes where
  interpret-ctx : Γ ⊢ctx → Ctx ★
  interpret-ty : (dT : Γ ⊢ty T) → Ty (interpret-ctx (valid-ty-to-ctx dT))
  -- Dominique: I would propose a different type:
  --   interpret-ty : (dΓ : Γ ⊢ctx) (dT : Γ ⊢ty T) → Ty (interpret-ctx dΓ)
  -- I think this might prevent the problem below in interpret-ty (d-⇛ dT dS) and interpret-ty (d-⊠ dT dS) and interpret-ty (d-Id dΓ dt ds)
  interpret-tm : (dt : Γ ⊢ t ∈ T) → Tm (interpret-ctx (valid-tm-to-ctx dt)) (interpret-ty (valid-tm-to-ty dt))
  -- Dominique: same here:
  -- interpret-tm : (dΓ : Γ ⊢ctx) (dT : Γ ⊢ty T) (dt : Γ ⊢ t ∈ T) → Tm (interpret-ctx dΓ) (interpret-ty dT)

  interpret-ctx d-◇ = M.◇
  interpret-ctx (d-,, dΓ dT) = interpret-ctx (valid-ty-to-ctx dT) M.,, interpret-ty dT

  interpret-ty (d-Nat _) = M.Nat'
  interpret-ty (d-Bool _) = M.Bool'
  interpret-ty (d-⇛ dT dS) = interpret-ty dT M.⇛ {!interpret-ty dS!}
  interpret-ty (d-⊠ dT dS) = interpret-ty dT M.⊠ {!interpret-ty dS!}
  interpret-ty (d-Id dΓ dt ds) = {!!} -- M-id.Id interpret-tm dt interpret-tm ds
  interpret-ty (d-ty-subst dT dσ) = {!!} -- interpret-ty dT M.[ {!!} ]
  -- Dominique: This breaks termination because the type of interpret-ty mentions the recursive call (interpret-ctx (validTy-to-ctx (d-ty-subst dT dσ))), which is passed as an implicit argument to _M.[_].
  -- Perhaps this can be already avoided by the change in the type of interpret-ty proposed above?
  -- Perhaps d-ty-subst can be made to additionally include a validity judgement of the context?

  interpret-tm dt = {!!}


module AllContextsTypes where
  interpret-ctx : Γ ⊢ctx → Ctx ★
  interpret-subst : (dΓ : Γ ⊢ctx) (dΔ : Δ ⊢ctx) → Γ ⊢ σ ⇒ Δ → interpret-ctx dΓ M.⇒ interpret-ctx dΔ
  interpret-ty : (dΓ : Γ ⊢ctx) → Γ ⊢ty T → Ty (interpret-ctx dΓ)
  interpret-tm : (dΓ : Γ ⊢ctx) (dT : Γ ⊢ty T) → Γ ⊢ t ∈ T → Tm (interpret-ctx dΓ) (interpret-ty dΓ dT)

  interpret-ctx d-◇ = M.◇
  interpret-ctx (d-,, dΓ dT) = interpret-ctx dΓ M.,, interpret-ty dΓ dT

  interpret-subst dΓ dΔ dσ = {!!}

  interpret-ty dΓ (d-Nat _) = M.Nat'
  interpret-ty dΓ (d-Bool _) = M.Bool'
  interpret-ty dΓ (d-⇛ dT dS) = interpret-ty dΓ dT M.⇛ interpret-ty dΓ dS
  interpret-ty dΓ (d-⊠ dT dS) = interpret-ty dΓ dT M.⊠ interpret-ty dΓ dS
  interpret-ty dΓ (d-Id _ dt ds) = M.Id (interpret-tm dΓ {!!} dt) (interpret-tm dΓ {!!} ds)
  interpret-ty dΓ (d-ty-subst dT dσ) = interpret-ty {!!} dT M.[ interpret-subst dΓ {!!} dσ ]

  interpret-tm dΓ dT (d-var _ dx) = {!!}
  interpret-tm dΓ dT (d-lam dt) = {!!}
  interpret-tm dΓ dT (d-app df dt) = M.app (interpret-tm dΓ {!!} df) (interpret-tm dΓ {!!} dt)
  interpret-tm dΓ dT (d-lit x) = {!!}
  interpret-tm dΓ dT (d-suc x) = {!!}
  interpret-tm dΓ dT (d-plus x) = {!!}
  interpret-tm dΓ dT (d-true x) = {!!}
  interpret-tm dΓ dT (d-false x) = {!!}
  interpret-tm dΓ dT (d-if dt dt₁ dt₂) = {!!}
  interpret-tm dΓ (d-⊠ dT dS) (d-pair dt ds) = M.pair $ interpret-tm dΓ dT dt $ interpret-tm dΓ dS ds
  interpret-tm dΓ dT (d-fst dp) = M.fst $ interpret-tm dΓ {!!} dp
  interpret-tm dΓ dT (d-snd dt) = {!!}
  interpret-tm dΓ dT (d-refl dt) = {!!}
  interpret-tm dΓ dT (d-tm-subst dt x) = {!!}
