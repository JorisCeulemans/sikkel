module Experimental.DeepEmbedding.Generic.Test where

open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit.Polymorphic

data Mode : Set where
  ★ : Mode
  ω : Mode

private
  variable
    m m' : Mode

data MetaMode (n : ℕ) : Set where
  lit : Mode → MetaMode n
  var : Fin n → MetaMode n

data CustomType : (n : ℕ) → List (MetaMode n) → MetaMode n → Set where
  CT0 : CustomType 0 [] (lit ω)
    -- ^ Intended interpretation is CT0 : Type ω
  CT1 : CustomType 1 (var (# 0) ∷ lit ω ∷ []) (var (# 0))
    -- ^ CT1 : ∀ {m} → Type m → Type ω → Type m

ModeEnv : ℕ → Set
ModeEnv zero = ⊤
ModeEnv (suc n) = Mode × ModeEnv n

lookup-mode : {n : ℕ} → Fin n → ModeEnv n → Mode
lookup-mode zero    ms = proj₁ ms
lookup-mode (suc i) ms = lookup-mode i (proj₂ ms)

to-mode : ∀ {n} → MetaMode n → ModeEnv n → Mode
to-mode (lit m) menv = m
to-mode (var x) menv = lookup-mode x menv

data Type : Mode → Set
ConstructorArgs : {n : ℕ} → ModeEnv n → List (MetaMode n) → Set

ConstructorArgs menv [] = ⊤
ConstructorArgs menv (mm ∷ ms) = Type (to-mode mm menv) × ConstructorArgs menv ms

data Type where
  _⇒_ : Type m → Type m → Type m
  Stream : Type ω → Type ω
  custom : ∀ {n ms m} → CustomType n ms m → {menv : ModeEnv n} → ConstructorArgs menv ms → Type (to-mode m menv)

SemDomain : Mode → Set₁
SemDomain _ = Set

SemDomainExt : ∀ {n} → MetaMode n → ModeEnv n → Set₁
SemDomainExt mm menv = SemDomain (to-mode mm menv)

TyInterpretResult : ∀ {n} (menv : ModeEnv n) → List (MetaMode n) → MetaMode n → Set₁
TyInterpretResult menv [] m = SemDomainExt m menv
TyInterpretResult menv (mm ∷ ms) m = SemDomainExt mm menv → TyInterpretResult menv ms m

module _ (F : ∀ {n ms m} {menv : ModeEnv n} → CustomType n ms m → TyInterpretResult menv ms m) where
  ⟦_⟧ty : Type m → SemDomain m
  interpret-custom : ∀ {n ms m} {menv : ModeEnv n} → TyInterpretResult menv ms m → ConstructorArgs menv ms → SemDomainExt m menv

  ⟦ T1 ⇒ T2 ⟧ty = ⟦ T1 ⟧ty → ⟦ T2 ⟧ty
  ⟦ Stream T ⟧ty = List ⟦ T ⟧ty
  ⟦_⟧ty (custom {m = m} c {menv = menv} args) = interpret-custom {m = m} (F {menv = menv} c) args

  interpret-custom {ms = []} G cargs = G
  interpret-custom {ms = mc ∷ ms} {m = m} G (carg , cargs) = interpret-custom {m = m} (G ⟦ carg ⟧ty) cargs
