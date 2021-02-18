--------------------------------------------------
-- Definition of the tactic by-naturality
--------------------------------------------------

module Reflection.Tactic.Naturality where

open import Data.List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product
open import Data.Unit
open import Reflection
open import Relation.Binary.PropositionalEquality

open import CwF-Structure
open import Reflection.Naturality.Solver renaming (reduce to nat-reduce)
open import Reflection.Tactic.ConstructExpression

get-equality-sides : Type → Maybe (Term × Term)
get-equality-sides (def (quote _≅ᵗʸ_) xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
get-equality-sides _ = nothing

by-naturality-macro : Term → TC ⊤
by-naturality-macro hole = do
  goal ← inferType hole
  debugPrint "vtac" 5 (strErr "naturality solver called, goal:" ∷ termErr goal ∷ [])
  just (lhs , rhs) ← return (get-equality-sides goal)
    where nothing → typeError (termErr goal ∷ strErr "is not a type equality." ∷ [])
  lhs-exp ← construct-expr lhs
  rhs-exp ← construct-expr rhs
  debugPrint "vtac" 5 (strErr "naturality solver successfully constructed expressions:" ∷ termErr lhs-exp ∷ termErr rhs-exp ∷ [])
  let sol = def (quote type-naturality-reflect)
                (vArg lhs-exp ∷ vArg rhs-exp ∷ vArg (con (quote _≡_.refl) []) ∷ vArg (con (quote _≡_.refl) []) ∷ [])
  unify hole sol

macro
  by-naturality : Term → TC ⊤
  by-naturality = by-naturality-macro
