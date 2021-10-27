module Experimental.DependentTypes.DeepEmbedding.Alternative2 where

open import Data.Nat renaming (_≟_ to _≟nat_)
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Model.BaseCategory as M
open import Model.CwF-Structure as M hiding (_,,_)
open import Model.Type.Discrete as M
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

import Experimental.DependentTypes.Model.IdentityType
module M-id = Experimental.DependentTypes.Model.IdentityType.Alternative1
open M-id hiding (Id)

open import Experimental.DependentTypes.DeepEmbedding.Syntax.AnnotatedIdentity
open import MSTT.TCMonad


-- TODO: Use of de Bruijn indices is incorrect, e.g. shift needed when extending context.

is-yes : ∀ {ℓ} {A : Set ℓ} → Dec A → TCM ⊤
is-yes (yes _) = return tt
is-yes (no _)  = type-error ""

_≟tm_ : TmExpr → TmExpr → TCM ⊤
_≟ty_ : TyExpr → TyExpr → TCM ⊤

(ann t ∈ T) ≟tm (ann s ∈ S) = (t ≟tm s) >> (T ≟ty S)
var x ≟tm var y = is-yes (x ≟nat y)
lam T b ≟tm lam S c = (T ≟ty S) >> (b ≟tm c)
(t1 ∙ s1) ≟tm (t2 ∙ s2) = (t1 ≟tm t2) >> (s1 ≟tm s2)
lit n ≟tm lit m = is-yes (n ≟nat m)
suc ≟tm suc = return tt
plus ≟tm plus = return tt
true ≟tm true = return tt
false ≟tm false = return tt
if c t f ≟tm if c' t' f' = (c ≟tm c') >> (t ≟tm t') >> (f ≟tm f')
pair t1 s1 ≟tm pair t2 s2 = (t1 ≟tm t2) >> (s1 ≟tm s2)
fst p1 ≟tm fst p2 = p1 ≟tm p2
snd p1 ≟tm snd p2 = p1 ≟tm p2
refl t ≟tm refl s = t ≟tm s
t ≟tm s = type-error ""

Nat ≟ty Nat = return tt
Bool ≟ty Bool = return tt
(T1 ⇛ S1) ≟ty (T2 ⇛ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
(T1 ⊠ S1) ≟ty (T2 ⊠ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
Id T1 t1 s1 ≟ty Id T2 t2 s2 = (T1 ≟ty T2) >> (t1 ≟tm t2) >> (s1 ≟tm s2)
T ≟ty S = type-error ""

lookup-var : ℕ → CtxExpr → TCM TyExpr
lookup-var x ◇ = type-error ""
lookup-var zero    (Γ ,, T) = return T
lookup-var (suc x) (Γ ,, T) = lookup-var x Γ

infer-type : TmExpr → CtxExpr → TCM TyExpr
infer-type (ann t ∈ S) Γ = do
  T ← infer-type t Γ
  T ≟ty S
  return S
infer-type (var x) Γ = lookup-var x Γ
infer-type (lam T b) Γ = do
  S ← infer-type b (Γ ,, T)
  return (T ⇛ S)
infer-type (t1 ∙ t2) Γ = do
  T1 ← infer-type t1 Γ
  fun-ty T S ← is-fun-ty T1
  T2 ← infer-type t2 Γ
  T2 ≟ty T
  return S
infer-type (lit n) Γ = return Nat
infer-type suc Γ = return (Nat ⇛ Nat)
infer-type plus Γ = return (Nat ⇛ Nat ⇛ Nat)
infer-type true Γ = return Bool
infer-type false Γ = return Bool
infer-type (if c t f) Γ = do
  C ← infer-type c Γ
  C ≟ty Bool
  T ← infer-type t Γ
  F ← infer-type f Γ
  T ≟ty F
  return T
infer-type (pair t1 t2) Γ = do
  T1 ← infer-type t1 Γ
  T2 ← infer-type t2 Γ
  return (T1 ⊠ T2)
infer-type (fst p) Γ = do
  P ← infer-type p Γ
  prod-ty T S ← is-prod-ty P
  return T
infer-type (snd p) Γ = do
  P ← infer-type p Γ
  prod-ty T S ← is-prod-ty P
  return S
infer-type (refl t) Γ = do
  T ← infer-type t Γ
  return (Id T t t)


infix 3 _⊢_∈_
_⊢_∈_ : CtxExpr → TmExpr → TyExpr → Set
Γ ⊢ t ∈ T = infer-type t Γ ≡ ok T

infix 3 _⊢ctx _⊢ty_
_⊢ctx : CtxExpr → Set
_⊢ty_ : CtxExpr → TyExpr → Set

◇ ⊢ctx = ⊤
Γ ,, T ⊢ctx = Γ ⊢ctx × Γ ⊢ty T

_ ⊢ty Nat = ⊤
_ ⊢ty Bool = ⊤
Γ ⊢ty T ⇛ S = Γ ⊢ty T × Γ ⊢ty S
Γ ⊢ty T ⊠ S = Γ ⊢ty T × Γ ⊢ty S
Γ ⊢ty Id R t s = (Γ ⊢ty R) × (Γ ⊢ t ∈ R) × (Γ ⊢ s ∈ R)

weaken-ty : {Γ : CtxExpr} (A T : TyExpr) → Γ ⊢ty T → Γ ,, A ⊢ty T
weaken-ty A Nat Γ⊢T = tt
weaken-ty A Bool Γ⊢T = tt
weaken-ty A (T ⇛ S) (Γ⊢T , Γ⊢S) = weaken-ty A T Γ⊢T , weaken-ty A S Γ⊢S
weaken-ty A (T ⊠ S) (Γ⊢T , Γ⊢S) = weaken-ty A T Γ⊢T , weaken-ty A S Γ⊢S
weaken-ty A (Id R t s) (Γ⊢R , Γ⊢t∈R , Γ⊢s∈R) = weaken-ty A R Γ⊢R , {!!} , {!!}

interpret-ctx : (Γ : CtxExpr) → Γ ⊢ctx → Ctx ★
interpret-ty : (T : TyExpr) {Γ : CtxExpr} → Γ ⊢ty T → {Γ-ok : Γ ⊢ctx} → Ty (interpret-ctx Γ Γ-ok)
interpret-tm : (t : TmExpr) {Γ : CtxExpr} {Γ-ok : Γ ⊢ctx} (T : TyExpr) (T-ok : Γ ⊢ty T) →
               Γ ⊢ t ∈ T → Tm (interpret-ctx Γ Γ-ok) (interpret-ty T T-ok)

interpret-ctx ◇ Γ-ok = M.◇
interpret-ctx (Γ ,, T) (Γ-ok , T-ok) = interpret-ctx Γ Γ-ok M.,, interpret-ty T T-ok

interpret-ty Nat T-ok = M.Nat'
interpret-ty Bool T-ok = M.Bool'
interpret-ty (T ⇛ S) (T-ok , S-ok) = interpret-ty T T-ok M.⇛ interpret-ty S S-ok
interpret-ty (T ⊠ S) (T-ok , S-ok) = interpret-ty T T-ok M.⊠ interpret-ty S S-ok
interpret-ty (Id R t s) (R-ok , t∈R , s∈R) = M-id.Id (interpret-tm t R R-ok t∈R)
                                                     (interpret-tm s R R-ok s∈R)

interpret-tm (ann t ∈ S) T T-ok t∈T = {!!}
interpret-tm (var x) T T-ok t∈T = {!!}
interpret-tm (lam A t) {Γ} S S-ok t∈T with infer-type t (Γ ,, A) in t∈T
interpret-tm (TmExpr.lam A t) {Γ} .(A ⇛ T) (A-ok , T-ok) refl | ok T = M.lam _ {!interpret-tm t {!T!} {!!} {!t∈T!}!}
interpret-tm (f ∙ t) S T-ok t∈T = {!!}
interpret-tm (lit n) .Nat T-ok refl = M.discr n
interpret-tm suc .(Nat ⇛ Nat) T-ok refl = M.suc'
interpret-tm plus .(Nat ⇛ Nat ⇛ Nat) T-ok refl = M.nat-sum
interpret-tm true .Bool T-ok refl = M.true'
interpret-tm false .Bool T-ok refl = M.false'
interpret-tm (if c t f) T T-ok t∈T = {!!}
interpret-tm (pair t s) T T-ok t∈T = {!!}
interpret-tm (fst p) T T-ok t∈T = {!!}
interpret-tm (snd p) T T-ok t∈T = {!!}
interpret-tm (refl t) {Γ} T T-ok t∈T with infer-type t Γ
interpret-tm (refl t) {_} .(Id S t t) T-ok refl | ok S = {!M-id.refl' {A = ?} ?!}
