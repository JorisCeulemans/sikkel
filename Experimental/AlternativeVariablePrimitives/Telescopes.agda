--------------------------------------------------
-- Definition and use of telescopes in a context
--------------------------------------------------

open import Categories

module Experimental.AlternativeVariablePrimitives.Telescopes {C : Category} where

open import Data.Fin
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding ([_]; _++_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (subst to transport)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import Experimental.AlternativeVariablePrimitives.ContextExtension

private
  variable
    Γ : Ctx C
    n : ℕ


var-type′ : (Ts : Telescope Γ n) (x : Fin n) → Ty (Γ ++ Ts)
var-type′ Ts x = lookupTel x Ts [ πs (suc x) Ts ]

prim-var′ : (Ts : Telescope Γ n) (x : Fin n) → Tm (Γ ++ Ts) (var-type′ Ts x)
prim-var′ Ts x = ξs x Ts

--------------------------------------------------
-- A telescope of length n can be used to denote variables
-- as de Bruijn indices using elements of type Fin n.

var-type : (Ts : Telescope Γ n) (x : Fin n) → Ty (Γ ++ Ts)
var-type (Ts ∷ T) zero    = T [ π ]
var-type (Ts ∷ T) (suc x) = (var-type Ts x) [ π ]

-- Not for direct use. See Reflection.Tactic.Telescopes.
prim-var : (Ts : Telescope Γ n) (x : Fin n) → Tm (Γ ++ Ts) (var-type Ts x)
prim-var (Ts ∷ T) zero    = ξ
prim-var (Ts ∷ T) (suc x) = (prim-var Ts x) [ π ]'


--------------------------------------------------
-- Using a telescope to define weakening of types and terms.

weaken-type : {Γ : Ctx C} {n : ℕ} (Ts : Telescope Γ n) →
              Ty Γ → Ty (Γ ++ Ts)
weaken-type []       S = S
weaken-type (Ts ∷ T) S = (weaken-type Ts S) [ π ]

-- Not for direct use. See Reflection.Tactic.Telescopes.
weaken-term : {Γ : Ctx C} {n : ℕ} (Ts : Telescope Γ n) {S : Ty Γ} →
              Tm Γ S → Tm (Γ ++ Ts) (weaken-type Ts S)
weaken-term []       s = s
weaken-term (Ts ∷ T) s = (weaken-term Ts s) [ π ]'
