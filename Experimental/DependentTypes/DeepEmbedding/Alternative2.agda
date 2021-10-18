module Experimental.DependentTypes.DeepEmbedding.Alternative2 where

open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M
open import Model.CwF-Structure as M hiding (_,,_)
open import Model.Type.Discrete as M
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

import Experimental.DependentTypes.Model.IdentityType
module M-id = Experimental.DependentTypes.Model.IdentityType.Alternative1
open M-id hiding (Id)

open import Experimental.DependentTypes.DeepEmbedding.Syntax
open import MSTT.TCMonad


infer-type : TmExpr → CtxExpr → TCM TyExpr
infer-type (ann t ∈ x) Γ = {!!}
infer-type (var x) Γ = {!!}
infer-type (lam x t) Γ = {!!}
infer-type (t ∙ t₁) Γ = {!!}
infer-type (lit x) Γ = {!!}
infer-type suc Γ = {!!}
infer-type plus Γ = {!!}
infer-type true Γ = return Bool
infer-type false Γ = {!!}
infer-type (if t t₁ t₂) Γ = {!!}
infer-type (pair t t₁) Γ = {!!}
infer-type (fst t) Γ = {!!}
infer-type (snd t) Γ = {!!}
infer-type (refl t) Γ = {!!}

_HasType_In_ : TmExpr → TyExpr → CtxExpr → Set
t HasType T In Γ = infer-type t Γ ≡ ok T

WellFormedCtx : CtxExpr → Set
WellFormedTy : TyExpr → CtxExpr → Set

WellFormedCtx ◇ = ⊤
WellFormedCtx (Γ ,, T) = WellFormedCtx Γ × WellFormedTy T Γ

WellFormedTy Nat _ = ⊤
WellFormedTy Bool _ = ⊤
WellFormedTy (T ⇛ S) Γ = WellFormedTy T Γ × WellFormedTy S Γ
WellFormedTy (T ⊠ S) Γ = WellFormedTy T Γ × WellFormedTy S Γ
WellFormedTy (Id t s) Γ = Σ[ T ∈ TyExpr ] Σ[ S ∈ TyExpr ] ((t HasType T In Γ) × (s HasType S In Γ) × T ≡ S)

inferred-well-formed : (t : TmExpr) (T : TyExpr) (Γ : CtxExpr) → t HasType T In Γ → WellFormedTy T Γ
inferred-well-formed t T Γ t∈T = {!!}

interpret-ctx : (Γ : CtxExpr) → WellFormedCtx Γ → Ctx ★
interpret-ty : (T : TyExpr) {Γ : CtxExpr} → WellFormedTy T Γ → {Γ-ok : WellFormedCtx Γ} → Ty (interpret-ctx Γ Γ-ok)
interpret-tm : (t : TmExpr) {Γ : CtxExpr} {Γ-ok : WellFormedCtx Γ} (T : TyExpr) (T-ok : WellFormedTy T Γ) →
               t HasType T In Γ → Tm (interpret-ctx Γ Γ-ok) (interpret-ty T T-ok)

interpret-ctx ◇ Γ-ok = M.◇
interpret-ctx (Γ ,, T) (Γ-ok , T-ok) = interpret-ctx Γ Γ-ok M.,, interpret-ty T T-ok

interpret-ty Nat T-ok = M.Nat'
interpret-ty Bool T-ok = M.Bool'
interpret-ty (T ⇛ S) (T-ok , S-ok) = interpret-ty T T-ok M.⇛ interpret-ty S S-ok
interpret-ty (T ⊠ S) (T-ok , S-ok) = interpret-ty T T-ok M.⊠ interpret-ty S S-ok
interpret-ty (Id t s) (T , S , t∈T , s∈S , T=S) = M-id.Id (interpret-tm t T (inferred-well-formed t T _ t∈T) t∈T)
                                                          (ι[ {!!} ] interpret-tm s S (inferred-well-formed s S _ s∈S) s∈S)

interpret-tm (ann t ∈ x) T T-ok t∈T = {!!}
interpret-tm (var x) T T-ok t∈T = {!!}
interpret-tm (TmExpr.lam x t) T T-ok t∈T = {!!}
interpret-tm (t ∙ t₁) T T-ok t∈T = {!!}
interpret-tm (lit x) T T-ok t∈T = {!!}
interpret-tm suc T T-ok t∈T = {!!}
interpret-tm plus T T-ok t∈T = {!!}
interpret-tm true .Bool T-ok refl = {!M.true'!}
interpret-tm false T T-ok t∈T = {!!}
interpret-tm (if t t₁ t₂) T T-ok t∈T = {!!}
interpret-tm (TmExpr.pair t t₁) T T-ok t∈T = {!!}
interpret-tm (TmExpr.fst t) T T-ok t∈T = {!!}
interpret-tm (TmExpr.snd t) T T-ok t∈T = {!!}
interpret-tm (refl t) T T-ok t∈T = {!!}
