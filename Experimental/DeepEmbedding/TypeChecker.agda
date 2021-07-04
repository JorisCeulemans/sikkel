open import Categories

module Experimental.DeepEmbedding.TypeChecker {C : Category} where

open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat
open import Data.Unit

open import CwF-Structure
open import Types.Functions
open import Types.Discrete

private
  variable
    n : ℕ


data TyExpr : Set where
  e-bool : TyExpr
  _e→_ : (e1 e2 : TyExpr) → TyExpr

data CtxExpr : ℕ → Set where
  e-◇ : CtxExpr 0
  _,_ : ∀ {n} → (Γ : CtxExpr n) (T : TyExpr) → CtxExpr (1 + n)

data TmExpr : ℕ → Set where
  e-var : Fin n → TmExpr n
  e-lam : TyExpr → TmExpr (1 + n) → TmExpr n
  e-app : TmExpr n → TmExpr n → TmExpr n
  e-true e-false : ∀ {n} → TmExpr n
  e-if : TmExpr n → TmExpr n → TmExpr n → TmExpr n


⟦_⟧ty : TyExpr → ClosedType C
⟦ e-bool ⟧ty = Bool'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty

⟦_⟧ctx : CtxExpr n → Ctx C
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty

lookup-ctx : Fin n → CtxExpr n → TyExpr
lookup-ctx zero    (Γ , T) = T
lookup-ctx (suc i) (Γ , T) = lookup-ctx i Γ

infer-type : TmExpr n → CtxExpr n → Maybe TyExpr
infer-type (e-var x) Γ = just (lookup-ctx x Γ)
infer-type (e-lam T b) Γ = do
  codomain ← infer-type b (Γ , T)
  just (T e→ codomain)
infer-type (e-app t1 t2) Γ = {!!}
infer-type e-true Γ = {!!}
infer-type e-false Γ = {!!}
infer-type (e-if t t₁ t₂) Γ = {!!}

semantic-type : TmExpr n → CtxExpr n → Set
semantic-type t Γ = maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)

⟦_⟧tm-in_ : (t : TmExpr n) (Γ : CtxExpr n) → semantic-type t Γ
⟦ e-var zero    ⟧tm-in (Γ , T) = {!!}
⟦ e-var (suc x) ⟧tm-in (Γ , T) = {!!}
⟦ e-lam x t ⟧tm-in Γ = {!!}
⟦ e-app t t₁ ⟧tm-in Γ = {!!}
⟦ e-true ⟧tm-in Γ = {!!}
⟦ e-false ⟧tm-in Γ = {!!}
⟦ e-if t t₁ t₂ ⟧tm-in Γ = {!!}
