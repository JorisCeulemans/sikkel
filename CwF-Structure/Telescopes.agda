{-# OPTIONS --without-K --omega-in-omega #-}

--------------------------------------------------
-- Definition and use of telescopes in a context
--
-- Note that we use the option omega-in-omega in order to define
-- an inductive data type in Setω and to pattern match on it (which
-- is not possible in Agda 2.6.1 without this option). This code should
-- typecheck without this option in Agda 2.6.2 once released.
--------------------------------------------------

open import Categories

module CwF-Structure.Telescopes {C : Category} where

open import Data.Fin
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding ([_]; _++_)
open import Level renaming (zero to lzero; suc to lsuc)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

private
  variable
    ℓ ℓ' ℓc ℓt r rc rt : Level
    Γ : Ctx C ℓ r
    n : ℕ
    ℓs rs : Vec Level n


--------------------------------------------------
-- Definition of a telescope in a context of a certain length

max-level : ∀ {n} → Vec Level n → Level
max-level = foldr _ _⊔_ 0ℓ

-- A value of Telescope Γ n ℓs is a list of types Ts = [] ∷ T1 ∷ T2 ∷ ... ∷ Tn so that
-- T1 is valid in Γ, T2 is valid in Γ ,, T1 etc. and hence Γ ,, T1 ,, T2 ,, ... ,, Tn
-- is a valid context written as Γ ++ Ts.
data Telescope (Γ : Ctx C ℓc rc) : (n : ℕ) → Vec Level n → Vec Level n → Setω
_++_ : (Γ : Ctx C ℓc rc) {n : ℕ} {ℓs rs : Vec Level n} → Telescope Γ n ℓs rs → Ctx C (ℓc ⊔ max-level ℓs) (rc ⊔ max-level rs)

data Telescope Γ where
  []  : Telescope Γ 0 [] []
  _∷_ : ∀ {ℓt n ℓs rs} (Ts : Telescope Γ n ℓs rs) → Ty (Γ ++ Ts) ℓt rt → Telescope Γ (suc n) (ℓt ∷ ℓs) (rt ∷ rs)

Γ ++ []       = Γ
Γ ++ (Ts ∷ T) = (Γ ++ Ts) ,, T


--------------------------------------------------
-- A telescope of length n can be used to denote variables
-- as de Bruijn indices using elements of type Fin n.

var-type : (Ts : Telescope Γ n ℓs rs) (x : Fin n) → Ty (Γ ++ Ts) (lookup ℓs x) (lookup rs x)
var-type (Ts ∷ T) zero    = T [ π ]
var-type (Ts ∷ T) (suc x) = (var-type Ts x) [ π ]

-- Not for direct use. See Reflection.Tactic.Telescopes.
prim-var : (Ts : Telescope Γ n ℓs rs) (x : Fin n) → Tm (Γ ++ Ts) (var-type Ts x)
prim-var (Ts ∷ T) zero    = ξ
prim-var (Ts ∷ T) (suc x) = (prim-var Ts x) [ π ]'


--------------------------------------------------
-- Using a telescope to define weakening of types and terms.

weaken-type : {Γ : Ctx C ℓc rc} {n : ℕ} {ℓs rs : _} (Ts : Telescope Γ n ℓs rs) →
              Ty Γ ℓt rt → Ty (Γ ++ Ts) ℓt rt
weaken-type []       S = S
weaken-type (Ts ∷ T) S = (weaken-type Ts S) [ π ]

-- Not for direct use. See Reflection.Tactic.Telescopes.
weaken-term : {Γ : Ctx C ℓc rc} {n : ℕ} {ℓs rs : _} (Ts : Telescope Γ n ℓs rs) {S : Ty Γ ℓt rt} →
              Tm Γ S → Tm (Γ ++ Ts) (weaken-type Ts S)
weaken-term []       s = s
weaken-term (Ts ∷ T) s = (weaken-term Ts s) [ π ]'
