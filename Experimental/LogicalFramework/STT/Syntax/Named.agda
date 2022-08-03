--------------------------------------------------
-- Instantiation of the general STT syntax with strings as names
--------------------------------------------------

module Experimental.LogicalFramework.STT.Syntax.Named where

open import Data.Empty
open import Data.String as Str
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality


--------------------------------------------------
-- Re-exporting the definitions of types, contexts, terms and associated operations.

open import Experimental.LogicalFramework.STT.Syntax.Types public
open import Experimental.LogicalFramework.STT.Syntax.General String public

private variable
  Γ : CtxExpr
  T S : TyExpr
  x y : String


--------------------------------------------------
-- Constructing a variable term by only mentioning the variable name
--   (i.e. resolving the De Bruijn index automatically).
--   This works via a decision procedure for Var x Γ.

vpred : ¬ (x ≡ y) → Var x (Γ ,, y ∈ S) → Var x Γ
vpred ¬x=y vzero    = ⊥-elim (¬x=y refl)
vpred ¬x=y (vsuc v) = v

var? : (x : String) (Γ : CtxExpr) → Dec (Var x Γ)
var? x ◇ = no (λ ())
var? x (Γ ,, y ∈ T) with x Str.≟ y
var? x (Γ ,, .x ∈ T) | yes refl = yes vzero
var? x (Γ ,, y ∈ T)  | no ¬x=y = map′ vsuc (vpred ¬x=y) (var? x Γ)

var : (x : String) → {v : True (var? x Γ)} → TmExpr Γ (lookup-var (toWitness v))
var x {v} = var' x {toWitness v} {refl}
