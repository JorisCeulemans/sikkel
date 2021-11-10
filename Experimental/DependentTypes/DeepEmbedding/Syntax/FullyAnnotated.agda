module Experimental.DependentTypes.DeepEmbedding.Syntax.FullyAnnotated where

open import Data.Nat

open import MSTT.TCMonad


data TyExpr : Set
data TmExpr : Set

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr where
  Nat Bool : TyExpr
  _⇛_ _⊠_ : TyExpr → TyExpr → TyExpr
  Id : TyExpr → TmExpr → TmExpr → TyExpr

-- infixl 50 _∙_
data TmExpr where
  ann_∈_ : TmExpr → TyExpr → TmExpr
  var : ℕ → TmExpr
  lam : TyExpr → TmExpr → TmExpr
  app : TyExpr → TmExpr → TmExpr → TmExpr
  lit : ℕ → TmExpr
  suc plus : TmExpr
  true false : TmExpr
  if : TmExpr → TmExpr → TmExpr → TmExpr
  pair : TmExpr → TmExpr → TmExpr
  fst snd : TyExpr → TmExpr → TmExpr
  refl : TyExpr → TmExpr → TmExpr

infixl 4 _,,_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_ : (Γ : CtxExpr) → (T : TyExpr) → CtxExpr


data IsFunTy : TyExpr → Set where
  fun-ty : (T S : TyExpr) → IsFunTy (T ⇛ S)

is-fun-ty : (T : TyExpr) → TCM (IsFunTy T)
is-fun-ty (T ⇛ S) = ok (fun-ty T S)
is-fun-ty T = type-error ""

data IsProdTy : TyExpr → Set where
  prod-ty : (T S : TyExpr) → IsProdTy (T ⊠ S)

is-prod-ty : (T : TyExpr) → TCM (IsProdTy T)
is-prod-ty (T ⊠ S) = ok (prod-ty T S)
is-prod-ty T = type-error ""


shift-from : ℕ → ℕ → ℕ
shift-from zero    n = suc n
shift-from (suc m) zero = zero
shift-from (suc m) (suc n) = suc (shift-from m n)

weaken-ty-from : ℕ → TyExpr → TyExpr
weaken-tm-from : ℕ → TmExpr → TmExpr

weaken-ty-from n Nat = Nat
weaken-ty-from n Bool = Bool
weaken-ty-from n (T ⇛ S) = weaken-ty-from n T ⇛ weaken-ty-from n S
weaken-ty-from n (T ⊠ S) = weaken-ty-from n T ⊠ weaken-ty-from n S
weaken-ty-from n (Id T t s) = Id (weaken-ty-from n T) (weaken-tm-from n t) (weaken-tm-from n s)

weaken-tm-from n (ann t ∈ S) = ann (weaken-tm-from n t) ∈ weaken-ty-from n S
weaken-tm-from n (var x) = var (shift-from n x)
weaken-tm-from n (lam T b) = lam (weaken-ty-from n T) (weaken-tm-from (suc n) b)
weaken-tm-from n (app S f t) = app (weaken-ty-from n S) (weaken-tm-from n f) (weaken-tm-from n t)
weaken-tm-from n (lit m) = lit m
weaken-tm-from n suc = suc
weaken-tm-from n plus = plus
weaken-tm-from n true = true
weaken-tm-from n false = false
weaken-tm-from n (if b t f) = if (weaken-tm-from n b) (weaken-tm-from n t) (weaken-tm-from n f)
weaken-tm-from n (pair t s) = pair (weaken-tm-from n t) (weaken-tm-from n s)
weaken-tm-from n (fst P p) = fst (weaken-ty-from n P) (weaken-tm-from n p)
weaken-tm-from n (snd P p) = snd (weaken-ty-from n P) (weaken-tm-from n p)
weaken-tm-from n (refl T t) = refl (weaken-ty-from n T) (weaken-tm-from n t)

weaken-ty : TyExpr → TyExpr
weaken-ty = weaken-ty-from 0

weaken-tm : TmExpr → TmExpr
weaken-tm = weaken-tm-from 0
