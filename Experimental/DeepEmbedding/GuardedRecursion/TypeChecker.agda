module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker where

open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import Types.Instances
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded


-- Needed for the do-notation below to desugar properly (this operator is
--   not exported by Data.Maybe).
infixl 1 _>>_
_>>_ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → Maybe A → Maybe B → Maybe B
just _  >> x = x
nothing >> x = nothing


--------------------------------------------------
-- Expressions representing types, contexts and terms

infixr 4 _e→_
data TyExpr : Set where
  e-Nat : TyExpr
  _e→_ : TyExpr → TyExpr → TyExpr
  e▻' : TyExpr → TyExpr
  e-GStreamN : TyExpr

data CtxExpr : Set where
  e-◇ : CtxExpr
  _,_ : (Γ : CtxExpr) (T : TyExpr) → CtxExpr

data TmExpr : Set where
  e-var : ℕ → TmExpr
  e-lam : TyExpr → TmExpr → TmExpr
  e-app : TmExpr → TmExpr → TmExpr
  e-lit : ℕ → TmExpr
  e-suc e-plus : TmExpr
  e-next' : TmExpr → TmExpr
  e-löb : TyExpr → TmExpr → TmExpr
  e-cons e-head e-tail : TmExpr

get-dom-cod : (T : TyExpr) → Maybe (TyExpr × TyExpr)
get-dom-cod e-Nat = nothing
get-dom-cod (T1 e→ T2) = just (T1 , T2)
get-dom-cod (e▻' T) = nothing
get-dom-cod e-GStreamN = nothing

get-dom-cod-sound : {T T1 T2 : TyExpr} → get-dom-cod T ≡ just (T1 , T2) → T ≡ (T1 e→ T2)
get-dom-cod-sound {T1 e→ T2} refl = refl

e→injˡ : {T T' S S' : TyExpr} → (T e→ S) ≡ (T' e→ S') → T ≡ T'
e→injˡ refl = refl

e→injʳ : {T T' S S' : TyExpr} → (T e→ S) ≡ (T' e→ S') → S ≡ S'
e→injʳ refl = refl

e▻'-inj : {T S : TyExpr} → (e▻' T) ≡ (e▻' S) → T ≡ S
e▻'-inj refl = refl

_≟_ : (T1 T2 : TyExpr) → Dec (T1 ≡ T2)
e-Nat ≟ e-Nat = yes refl
e-Nat ≟ (_ e→ _) = no (λ ())
e-Nat ≟ (e▻' _) = no (λ ())
e-Nat ≟ e-GStreamN = no (λ ())
(_ e→ _) ≟ e-Nat = no (λ ())
(T1 e→ T2) ≟ (T3 e→ T4) with T1 ≟ T3 | T2 ≟ T4
(T1 e→ T2) ≟ (T1 e→ T2) | yes refl | yes refl = yes refl
(T1 e→ T2) ≟ (T1 e→ T4) | yes refl | no ne = no (λ e → ne (e→injʳ e))
(T1 e→ T2) ≟ (T3 e→ T4) | no ne    | _ = no (λ e → ne (e→injˡ e))
(_ e→ _) ≟ (e▻' _) = no (λ ())
(_ e→ _) ≟ e-GStreamN = no (λ ())
(e▻' T) ≟ e-Nat = no (λ ())
(e▻' T) ≟ (_ e→ _) = no (λ ())
(e▻' T) ≟ (e▻' S) with T ≟ S
(e▻' T) ≟ (e▻' .T) | yes refl = yes refl
(e▻' T) ≟ (e▻' S)  | no ne = no (λ e → ne (e▻'-inj e))
(e▻' T) ≟ e-GStreamN = no (λ ())
e-GStreamN ≟ e-Nat = no (λ ())
e-GStreamN ≟ (_ e→ _) = no (λ ())
e-GStreamN ≟ (e▻' _) = no (λ ())
e-GStreamN ≟ e-GStreamN = yes refl


--------------------------------------------------
-- Interpretation of types and contexts in a presheaf model

⟦_⟧ty : TyExpr → ClosedType ω
⟦ e-Nat ⟧ty = Nat'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty
⟦ e▻' T ⟧ty = ▻' ⟦ T ⟧ty
⟦ e-GStreamN ⟧ty = GStream Nat'

⟦_⟧ctx : CtxExpr → Ctx ω
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty

instance
  ⟦⟧ty-natural : {T : TyExpr} → IsClosedNatural ⟦ T ⟧ty
  ⟦⟧ty-natural {e-Nat} = discr-closed
  ⟦⟧ty-natural {T1 e→ T2} = fun-closed {{⟦⟧ty-natural {T1}}} {{⟦⟧ty-natural {T2}}}
  ⟦⟧ty-natural {e▻' T} = ▻'-closed {{⟦⟧ty-natural {T}}}
  ⟦⟧ty-natural {e-GStreamN} = gstream-closed


--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language

lookup-ctx : ℕ → CtxExpr → Maybe TyExpr
lookup-ctx x       e-◇ = nothing
lookup-ctx zero    (Γ , T) = just T
lookup-ctx (suc x) (Γ , T) = lookup-ctx x Γ

infer-type : TmExpr → CtxExpr → Maybe TyExpr
infer-type (e-var x) Γ = lookup-ctx x Γ
infer-type (e-lam T b) Γ =  do
  codomain ← infer-type b (Γ , T)
  just (T e→ codomain)
infer-type (e-app t1 t2) Γ = do
  T1 ← infer-type t1 Γ
  dom , cod ← get-dom-cod T1
  T2 ← infer-type t2 Γ
  decToMaybe (dom ≟ T2)
  just cod
infer-type (e-lit n) Γ = just e-Nat
infer-type e-suc Γ = just (e-Nat e→ e-Nat)
infer-type e-plus Γ = just (e-Nat e→ e-Nat e→ e-Nat)
infer-type (e-next' t) Γ = do
  T ← infer-type t Γ
  just (e▻' T)
infer-type (e-löb T t) Γ = do
  S ← infer-type t (Γ , e▻' T)
  decToMaybe (T ≟ S)
  just T
infer-type e-cons Γ = just (e-Nat e→ (e▻' e-GStreamN) e→ e-GStreamN)
infer-type e-head Γ = just (e-GStreamN e→ e-Nat)
infer-type e-tail Γ = just (e-GStreamN e→ (e▻' e-GStreamN))


--------------------------------------------------
-- Interpretation of terms that are accepted by the typechecker
-- in a presheaf model

semantic-type : TmExpr → CtxExpr → Set
semantic-type t Γ = maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)

interpret-var : (x : ℕ) (Γ : CtxExpr) → semantic-type (e-var x) Γ
interpret-var x e-◇ = tt
interpret-var zero (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural {T}}} π ] ξ
interpret-var (suc x) (Γ , T) with lookup-ctx x Γ | interpret-var x Γ
interpret-var (suc x) (Γ , T) | just S  | ⟦x⟧ = ι⁻¹[ closed-natural {{⟦⟧ty-natural {S}}} π ] (⟦x⟧ [ π ]')
interpret-var (suc x) (Γ , T) | nothing | ⟦x⟧ = tt

open import Reflection.Tactic.Lambda
⟦_⟧tm-in_ : (t : TmExpr) (Γ : CtxExpr) → semantic-type t Γ
⟦ e-var x ⟧tm-in Γ = interpret-var x Γ
⟦ e-lam T b ⟧tm-in Γ with infer-type b (Γ , T) | ⟦ b ⟧tm-in (Γ , T)
⟦ e-lam T b ⟧tm-in Γ | just S  | ⟦b⟧ = lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural {S}}} π ] ⟦b⟧)
⟦ e-lam T b ⟧tm-in Γ | nothing | ⟦b⟧ = tt
⟦ e-app t1 t2 ⟧tm-in Γ with infer-type t1 Γ | ⟦ t1 ⟧tm-in Γ
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ with get-dom-cod T1 | inspect get-dom-cod T1
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ | just (dom , cod) | [ e ] with infer-type t2 Γ | ⟦ t2 ⟧tm-in Γ
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ | just (dom , cod) | [ e ] | just T2 | ⟦t2⟧ with dom ≟ T2
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ | just (dom , cod) | [ e ] | just T2 | ⟦t2⟧ | yes refl = app (subst (λ - → Tm ⟦ Γ ⟧ctx ⟦ - ⟧ty) (get-dom-cod-sound e) ⟦t1⟧) ⟦t2⟧
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ | just (dom , cod) | [ e ] | just T2 | ⟦t2⟧ | no ne = tt
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ | just (dom , cod) | [ e ] | nothing | _ = tt
⟦ e-app t1 t2 ⟧tm-in Γ | just T1 | ⟦t1⟧ | nothing | _ = tt
⟦ e-app t1 t2 ⟧tm-in Γ | nothing | _ = tt
⟦ e-lit n ⟧tm-in Γ = discr n
⟦ e-suc ⟧tm-in Γ = suc'
⟦ e-plus ⟧tm-in Γ = nat-sum
⟦ e-next' t ⟧tm-in Γ with infer-type t Γ | ⟦ t ⟧tm-in Γ
⟦ e-next' t ⟧tm-in Γ | just T  | ⟦t⟧ = next' ⟦t⟧
⟦ e-next' t ⟧tm-in Γ | nothing | ⟦t⟧ = tt
⟦ e-löb T t ⟧tm-in Γ with infer-type t (Γ , e▻' T) | ⟦ t ⟧tm-in (Γ , e▻' T)
⟦ e-löb T t ⟧tm-in Γ | just S  | ⟦t⟧ with T ≟ S
⟦ e-löb T t ⟧tm-in Γ | just .T | ⟦t⟧ | yes refl = löb' ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural {T}}} π ] ⟦t⟧)
⟦ e-löb T t ⟧tm-in Γ | just S  | ⟦t⟧ | no ne = tt
⟦ e-löb T t ⟧tm-in Γ | nothing | ⟦t⟧ = tt
⟦ e-cons ⟧tm-in Γ = {!!}
⟦ e-head ⟧tm-in Γ = {!!}
⟦ e-tail ⟧tm-in Γ = {!!}
