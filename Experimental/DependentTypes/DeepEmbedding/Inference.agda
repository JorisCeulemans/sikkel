module Experimental.DependentTypes.DeepEmbedding.Inference where

open import Data.Nat renaming (_≟_ to _≟nat_)
open import Data.Unit hiding (_≟_)
open import Relation.Nullary

open import Experimental.DependentTypes.DeepEmbedding.Syntax
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
Id t1 s1 ≟ty Id t2 s2 = (t1 ≟tm t2) >> (s1 ≟tm s2)
T ≟ty S = type-error ""

lookup-var : ℕ → CtxExpr → TCM TyExpr
lookup-var x ◇ = type-error ""
lookup-var zero    (Γ ,, T) = return T
lookup-var (suc x) (Γ ,, T) = lookup-var x Γ

infer-tm : TmExpr → CtxExpr → TCM TyExpr
infer-tm (ann t ∈ S) Γ = do
  T ← infer-tm t Γ
  T ≟ty S
  return S
infer-tm (var x) Γ = lookup-var x Γ
infer-tm (lam T b) Γ = do
  S ← infer-tm b (Γ ,, T)
  return (T ⇛ S)
infer-tm (t1 ∙ t2) Γ = do
  T1 ← infer-tm t1 Γ
  fun-ty T S ← is-fun-ty T1
  T2 ← infer-tm t2 Γ
  T2 ≟ty T
  return S
infer-tm (lit n) Γ = return Nat
infer-tm suc Γ = return (Nat ⇛ Nat)
infer-tm plus Γ = return (Nat ⇛ Nat ⇛ Nat)
infer-tm true Γ = return Bool
infer-tm false Γ = return Bool
infer-tm (if c t f) Γ = do
  C ← infer-tm c Γ
  C ≟ty Bool
  T ← infer-tm t Γ
  F ← infer-tm f Γ
  T ≟ty F
  return T
infer-tm (pair t1 t2) Γ = do
  T1 ← infer-tm t1 Γ
  T2 ← infer-tm t2 Γ
  return (T1 ⊠ T2)
infer-tm (fst p) Γ = do
  P ← infer-tm p Γ
  prod-ty T S ← is-prod-ty P
  return T
infer-tm (snd p) Γ = do
  P ← infer-tm p Γ
  prod-ty T S ← is-prod-ty P
  return S
infer-tm (refl t) Γ = do
  infer-tm t Γ
  return (Id t t)

check-ty : TyExpr → CtxExpr → TCM ⊤
check-ty Nat Γ = return tt
check-ty Bool Γ = return tt
check-ty (T ⇛ S) Γ = check-ty T Γ >> check-ty S Γ
check-ty (T ⊠ S) Γ = check-ty T Γ >> check-ty S Γ
check-ty (Id t s) Γ = do
  T ← infer-tm t Γ
  S ← infer-tm s Γ
  T ≟ty S
