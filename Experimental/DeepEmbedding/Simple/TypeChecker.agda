open import Categories

module Experimental.DeepEmbedding.Simple.TypeChecker {C : Category} where

open import Data.Fin hiding (_+_; _≟_)
open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

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

data TmExpr (n : ℕ) : Set where
  e-var : Fin n → TmExpr n
  e-lam : TyExpr → TmExpr (1 + n) → TmExpr n
  e-app : TmExpr n → TmExpr n → TmExpr n
  e-true e-false : TmExpr n
  e-if : TmExpr n → TmExpr n → TmExpr n → TmExpr n


-- Deciding whether a type expression is a function type.

record IsFuncTyExpr (T : TyExpr) : Set where
  constructor func-ty
  field
    dom cod : TyExpr
    is-func : T ≡ dom e→ cod

is-func-ty : (T : TyExpr) → Maybe (IsFuncTyExpr T)
is-func-ty e-bool = nothing
is-func-ty (T1 e→ T2) = just (func-ty T1 T2 refl)


-- Decidable equality for type expressions.

e→injˡ : {T T' S S' : TyExpr} → (T e→ S) ≡ (T' e→ S') → T ≡ T'
e→injˡ refl = refl

e→injʳ : {T T' S S' : TyExpr} → (T e→ S) ≡ (T' e→ S') → S ≡ S'
e→injʳ refl = refl

_≟_ : (T1 T2 : TyExpr) → Dec (T1 ≡ T2)
e-bool ≟ e-bool = yes refl
e-bool ≟ (_ e→ _) = no (λ ())
(_ e→ _) ≟ e-bool = no (λ ())
(T1 e→ T2) ≟ (T3 e→ T4) with T1 ≟ T3 | T2 ≟ T4
(T1 e→ T2) ≟ (T1 e→ T2) | yes refl | yes refl = yes refl
(T1 e→ T2) ≟ (T1 e→ T4) | yes refl | no ne = no (λ e → ne (e→injʳ e))
(T1 e→ T2) ≟ (T3 e→ T4) | no ne    | _ = no (λ e → ne (e→injˡ e))


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
--   and interpretation of well-typed terms in a presheaf model

record InferInterpretResult (Γ : CtxExpr n) : Set where
  constructor _,_
  field
    type : TyExpr
    interpretation : Tm ⟦ Γ ⟧ctx ⟦ type ⟧ty

lookup-ctx : Fin n → (Γ : CtxExpr n) → InferInterpretResult Γ
lookup-ctx zero    (Γ , T) = T , (ι⁻¹[ closed-natural {{⟦⟧ty-natural {T}}} π ] ξ)
lookup-ctx (suc i) (Γ , T) =
  let S , ⟦var-i⟧ = lookup-ctx i Γ
  in  S , (ι⁻¹[ closed-natural {{⟦⟧ty-natural {S}}} π ] (⟦var-i⟧ [ π ]'))

infer-interpret : (t : TmExpr n) (Γ : CtxExpr n) → Maybe (InferInterpretResult Γ)
infer-interpret (e-var x) Γ = just (lookup-ctx x Γ)
infer-interpret (e-lam T b) Γ = do
  S , ⟦b⟧ ← infer-interpret b (Γ , T)
  just (T e→ S , lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural {S}}} π ] ⟦b⟧))
infer-interpret (e-app t1 t2) Γ = do
  T1 , ⟦t1⟧ ← infer-interpret t1 Γ
  func-ty dom cod refl ← is-func-ty T1
  T2 , ⟦t2⟧ ← infer-interpret t2 Γ
  refl ← decToMaybe (dom ≟ T2)
  just (cod , app ⟦t1⟧ ⟦t2⟧)
infer-interpret e-true Γ = just (e-bool , true')
infer-interpret e-false Γ = just (e-bool , false')
infer-interpret (e-if t-c t-t t-f) Γ = do
  T-c , ⟦t-c⟧ ← infer-interpret t-c Γ
  refl ← decToMaybe (T-c ≟ e-bool)
  T-t , ⟦t-t⟧ ← infer-interpret t-t Γ
  T-f , ⟦t-f⟧ ← infer-interpret t-f Γ
  refl ← decToMaybe (T-t ≟ T-f)
  just (T-t , if' ⟦t-c⟧ then' ⟦t-t⟧ else' ⟦t-f⟧)

infer-type : TmExpr n → CtxExpr n → Maybe TyExpr
infer-type t Γ = map InferInterpretResult.type (infer-interpret t Γ)

⟦_⟧tm-in_ : (t : TmExpr n) (Γ : CtxExpr n) → maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)
⟦ t ⟧tm-in Γ with infer-interpret t Γ
⟦ t ⟧tm-in Γ | just (T , ⟦t⟧) = ⟦t⟧
⟦ t ⟧tm-in Γ | nothing = tt
