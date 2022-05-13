module Experimental.ProgramLogic.InductionInduction.DependentTypesTest where

open import Data.Bool hiding (T)
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality


data CtxExpr : Set
data TyExpr : CtxExpr → Set
data TmExpr : (Γ : CtxExpr) → TyExpr Γ → Set
data TyEq : (Γ : CtxExpr) (T S : TyExpr Γ) → Set
data TmEq : (Γ : CtxExpr) (T : TyExpr Γ) (t s : TmExpr Γ T) → Set

private variable
  Γ : CtxExpr
  T : TyExpr Γ

data CtxExpr where
  ◇ : CtxExpr
  _,,_ : (Γ : CtxExpr) → TyExpr Γ → CtxExpr

data TyExpr where
  Bool' : TyExpr Γ
  Id : {T : TyExpr Γ} → (t s : TmExpr Γ T) → TyExpr Γ

data TmExpr where
  true false : TmExpr Γ Bool'
  if : {T : TyExpr Γ} → TmExpr Γ Bool' → TmExpr Γ T → TmExpr Γ T → TmExpr Γ T
  refl : {T : TyExpr Γ} → (t : TmExpr Γ T) → TmExpr Γ (Id t t)
  conv : {T S : TyExpr Γ} → TyEq Γ T S → TmExpr Γ T → TmExpr Γ S

data TyEq where
  Id-congˡ : {t t' s : TmExpr Γ T} → TmEq Γ T t t' → TyEq Γ (Id t s) (Id t' s)
  Id-congʳ : {t s s' : TmExpr Γ T} → TmEq Γ T s s' → TyEq Γ (Id t s) (Id t s')

data TmEq where
  if-β-true : {t s : TmExpr Γ T} → TmEq Γ T (if true t s) t
  if-β-false : {t s : TmExpr Γ T} → TmEq Γ T (if false t s) s

syntax TyEq Γ T S = Γ ⊢ T ≡ S
syntax TmEq Γ T t s = Γ ⊢ t ≡ s ∈ T

⟦_⟧ctx : CtxExpr → Set
⟦_⟧ty : TyExpr Γ → (⟦ Γ ⟧ctx → Set)
⟦_⟧tm : TmExpr Γ T → ((γ : ⟦ Γ ⟧ctx) → ⟦ T ⟧ty γ)
⟦_⟧ty-eq : {T S : TyExpr Γ} → Γ ⊢ T ≡ S → ((γ : ⟦ Γ ⟧ctx) → ⟦ T ⟧ty γ ≡ ⟦ S ⟧ty γ)
⟦_⟧tm-eq : {t s : TmExpr Γ T} → Γ ⊢ t ≡ s ∈ T → ((γ : ⟦ Γ ⟧ctx) → ⟦ t ⟧tm γ ≡ ⟦ s ⟧tm γ)

⟦ ◇ ⟧ctx = ⊤
⟦ Γ ,, T ⟧ctx = Σ ⟦ Γ ⟧ctx ⟦ T ⟧ty

⟦ Bool' ⟧ty _ = Bool
⟦ Id t s ⟧ty γ = ⟦ t ⟧tm γ ≡ ⟦ s ⟧tm γ

⟦ true ⟧tm _ = true
⟦ false ⟧tm _ = false
⟦ if b t f ⟧tm γ = if ⟦ b ⟧tm γ then ⟦ t ⟧tm γ else ⟦ f ⟧tm γ
⟦ refl t ⟧tm _ = refl
⟦ conv T=S t ⟧tm γ = subst (λ x → x) (⟦ T=S ⟧ty-eq γ) (⟦ t ⟧tm γ)

⟦ Id-congˡ {s = s} d ⟧ty-eq γ = cong (_≡ ⟦ s ⟧tm γ) (⟦ d ⟧tm-eq γ)
⟦ Id-congʳ {t = t} d ⟧ty-eq γ = cong (⟦ t ⟧tm γ ≡_) (⟦ d ⟧tm-eq γ)

⟦ if-β-true ⟧tm-eq γ = refl
⟦ if-β-false ⟧tm-eq γ = refl
