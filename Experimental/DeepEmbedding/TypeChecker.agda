open import Categories

module Experimental.DeepEmbedding.TypeChecker {C : Category} where

open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Nat
open import Data.Unit

open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import Types.Instances

private
  variable
    n : ℕ


--------------------------------------------------
-- Expressions representing types, contexts and terms

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


--------------------------------------------------
-- Interpretation of types and contexts in a presheaf model

⟦_⟧ty : TyExpr → ClosedType C
⟦ e-bool ⟧ty = Bool'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty

⟦_⟧ctx : CtxExpr n → Ctx C
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty

instance
  ⟦⟧ty-natural : {T : TyExpr} → IsClosedNatural ⟦ T ⟧ty
  ⟦⟧ty-natural {e-bool} = discr-closed
  ⟦⟧ty-natural {T1 e→ T2} = fun-closed {{⟦⟧ty-natural {T1}}} {{⟦⟧ty-natural {T2}}}


--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language

lookup-ctx : Fin n → CtxExpr n → TyExpr
lookup-ctx zero    (Γ , T) = T
lookup-ctx (suc i) (Γ , T) = lookup-ctx i Γ

infer-type : TmExpr n → CtxExpr n → Maybe TyExpr
infer-type (e-var x) Γ = just (lookup-ctx x Γ)
infer-type (e-lam T b) Γ = do
  codomain ← infer-type b (Γ , T)
  just (T e→ codomain)
infer-type (e-app t1 t2) Γ = {!!}
infer-type e-true Γ = just e-bool
infer-type e-false Γ = just e-bool
infer-type (e-if t-c t-t t-f) Γ = {!!}


--------------------------------------------------
-- Interpretation of terms that are accepted by the typechecker
-- in a presheaf model

semantic-type : TmExpr n → CtxExpr n → Set
semantic-type t Γ = maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)

open import Reflection.Tactic.Naturality
⟦_⟧tm-in_ : (t : TmExpr n) (Γ : CtxExpr n) → semantic-type t Γ
⟦ e-var zero    ⟧tm-in (Γ , T) = {!db-varι 0!}
⟦ e-var (suc x) ⟧tm-in (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural {lookup-ctx x Γ}}} π ] ((⟦ e-var x ⟧tm-in Γ) [ π ]')
⟦ e-lam T b ⟧tm-in Γ = {!!}
⟦ e-app t t₁ ⟧tm-in Γ = {!!}
⟦ e-true ⟧tm-in Γ = true'
⟦ e-false ⟧tm-in Γ = false'
⟦ e-if t t₁ t₂ ⟧tm-in Γ = {!!}
