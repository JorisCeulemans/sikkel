{-# OPTIONS --omega-in-omega #-}

open import Categories

module CwF-Structure.Variables {C : Category} where

open import Data.Fin
open import Data.Vec hiding ([_])
open import Data.Nat hiding (_⊔_)
open import Level renaming (suc to lsuc)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

private
  variable
    ℓ ℓ' ℓc : Level
    Γ : Ctx C ℓ
    n : ℕ
    ℓs : Vec Level n


level-fold : ∀ {n} → Vec Level n → Level
level-fold = foldr _ _⊔_ 0ℓ

data TypeSequence (Γ : Ctx C ℓc) : (n : ℕ) → Vec Level n →  Setω
_,,,_ : (Γ : Ctx C ℓc) {n : ℕ} {ℓs : Vec Level n} → TypeSequence Γ n ℓs → Ctx C (ℓc ⊔ level-fold ℓs)


data TypeSequence Γ where
  []  : TypeSequence Γ 0 []
  _∷_ : ∀ {ℓt n ℓs} (Ts : TypeSequence Γ n ℓs) → Ty (Γ ,,, Ts) ℓt → TypeSequence Γ (suc n) (ℓt ∷ ℓs)

Γ ,,, []       = Γ
Γ ,,, (Ts ∷ T) = (Γ ,,, Ts) ,, T

get-type : (Ts : TypeSequence Γ n ℓs) (x : Fin n) → Ty (Γ ,,, Ts) (lookup ℓs x)
get-type (Ts ∷ T) zero    = T [ π ]
get-type (Ts ∷ T) (suc x) = (get-type Ts x) [ π ]

var : (Ts : TypeSequence Γ n ℓs) (x : Fin n) → Tm (Γ ,,, Ts) (get-type Ts x)
var (Ts ∷ T) zero    = ξ
var (Ts ∷ T) (suc x) = var Ts x [ π ]'
