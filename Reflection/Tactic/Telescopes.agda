--------------------------------------------------
-- Definition of macros that enable working with
-- variables and weakening (see CwF-Structure.Telescopes)
-- without having to specify the telescope.
--------------------------------------------------

module Reflection.Tactic.Telescopes where

open import Data.Bool hiding (_<?_)
open import Data.Fin using (#_)
open import Data.List
open import Data.Nat
open import Data.Unit
open import Reflection hiding (var)
open import Reflection.TypeChecking.Monad.Syntax
open import Relation.Nullary.Decidable using (⌊_⌋)

open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import CwF-Structure.Telescopes
open import Reflection.Naturality renaming (reduce to nat-reduce)
open import Reflection.Tactic.ConstructExpression
open import Reflection.Tactic.Util

--------------------------------------------------
-- Definition of a function that automatically transforms the current
-- context into a telescope.

-- If get-ctx is applied to an Agda type of the form Tm Γ T, then
-- the context Γ is returned.
get-ctx : Type → TC Term
get-ctx (def (quote Tm) args) = get-visible-arg 0 args
get-ctx (meta m args) = debugPrint "vtac" 5 (strErr "Blocing on meta" ∷ termErr (meta m args) ∷ strErr "in get-ctx." ∷ []) >>
                        blockOnMeta m
get-ctx _ = typeError (strErr "get-ctx can only get the context of a term." ∷ [])

-- ctx-to-telescope takes a value of type Ctx C ℓ and transforms it into a type
-- sequence. If a context is of the form Γ ,, T then T is added to the type
-- sequence and ctx-to-telescope is called recursively on Γ. Otherwise the process
-- stops and ctx-to-telescope returns an empty sequence.
ctx-to-telescope : Term → TC Term
ctx-to-telescope (def (quote _,,_) xs) = go xs
  where
    go : List (Arg Term) → TC Term
    go [] = typeError (strErr "Invalid use of context extension." ∷ [])
    go (vArg ctx ∷ vArg ty ∷ xs) = (λ telescope → con (quote Telescope._∷_) (vArg telescope ∷ vArg ty ∷ [])) <$>
                                   (ctx-to-telescope ctx)
    go (_ ∷ xs) = go xs
ctx-to-telescope (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in ctx-to-telescope." ∷ []) >>
                                 blockOnMeta m
ctx-to-telescope _ = return (con (quote Telescope.[]) [])


--------------------------------------------------
-- Definition of the macro var that turns a context
-- into a telescope and applies prim-var.

-- Check whether the provided de Bruijn index is within bounds (i.e. does not
-- exceed the length of the telescope - 1).
check-within-bounds : Term → Term → TC ⊤
check-within-bounds t-index t-telescope = do
  index ← unquoteTC t-index
  def (quote Telescope) args ← inferType t-telescope
    where _ → typeError (strErr "An error occurred, this point should not be reached." ∷ [])
  t-telescope-len ← get-visible-arg 1 args
  telescope-len ← unquoteTC t-telescope-len
  go ⌊ index <? telescope-len ⌋ t-telescope-len
  where
    go : Bool → Term → TC ⊤
    go false len = typeError (strErr "The provided de Bruijn index" ∷ termErr t-index ∷
                              strErr " is too high. Number of available variables:" ∷ termErr len ∷ [])
    go true  _   = return tt

construct-var-solution : Term → Term → TC Term
construct-var-solution x hole = do
  goal ← inferType hole
  debugPrint "vtac" 5 (strErr "var macro called, goal:" ∷ termErr goal ∷ [])
  ctx ← get-ctx goal
  telescope ← ctx-to-telescope ctx
  check-within-bounds x telescope
  return (def (quote prim-var) (vArg telescope ∷ vArg (def (quote #_) (vArg x ∷ [])) ∷ []))

var-macro : Term → Term → TC ⊤
var-macro x hole = do
  solution ← construct-var-solution x hole
  debugPrint "vtac" 5 (strErr "var macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  var : Term → Term → TC ⊤
  var = var-macro


-------------------------------------------------
-- Variable macro that automatically performs naturality reduction on its type

varι-macro : Term → Term → TC ⊤
varι-macro x hole = do
  partialSolution ← construct-var-solution x hole
  expr-resultType ← inferType partialSolution >>= get-term-type >>= construct-expr
  let proof = def (quote reduce-sound) (vArg expr-resultType ∷ [])
  let solution = def (quote ι⁻¹[_]_) (vArg proof ∷ vArg partialSolution ∷ [])
  debugPrint "vtac" 5 (strErr "varι macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  varι : Term → Term → TC ⊤
  varι = varι-macro


-------------------------------------------------
-- Definition of a macro that performs weakening of terms
-- and infers the telescope itself from the current context.

bounded-ctx-to-telescope : ℕ → Term → TC Term
bounded-ctx-to-telescope 0       _ = return (con (quote Telescope.[]) [])
bounded-ctx-to-telescope (suc n) (def (quote _,,_) xs) = go xs
  where
    go : List (Arg Term) → TC Term
    go [] = typeError (strErr "Invalid use of context extension." ∷ [])
    go (vArg ctx ∷ vArg ty ∷ xs) = (λ telescope → con (quote Telescope._∷_) (vArg telescope ∷ vArg ty ∷ [])) <$>
                                   (bounded-ctx-to-telescope n ctx)
    go (_ ∷ xs) = go xs
bounded-ctx-to-telescope (suc n) (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in ctx-to-telescope." ∷ []) >>
                                                 blockOnMeta m
bounded-ctx-to-telescope (suc n) _ = typeError (strErr "Weakening this far is not possible in the current context." ∷ [])

construct-weaken-solution : ℕ → Term → Term → TC Term
construct-weaken-solution n term hole = do
  goal ← inferType hole
  debugPrint "vtac" 5 (strErr "↑ macro called, goal:" ∷ termErr goal ∷ [])
  extended-ctx ← get-ctx goal
  ty-seq ← bounded-ctx-to-telescope n extended-ctx
  return (def (quote weaken-term) (vArg ty-seq ∷ vArg term ∷ []))

weaken-macro : ℕ → Term → Term → TC ⊤
weaken-macro n term hole = do
  solution ← construct-weaken-solution n term hole
  debugPrint "vtac" 5 (strErr "↑ macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  ↑⟨_⟩_ : ℕ → Term → Term → TC ⊤
  ↑⟨ n ⟩ term = weaken-macro n term


-------------------------------------------------
-- Weakening macro that automatically performs naturality reduction on its type

weakenι-macro : ℕ → Term → Term → TC ⊤
weakenι-macro n term hole = do
  partial-solution ← construct-weaken-solution n term hole
  expr-resultType ← inferType partial-solution >>= get-term-type >>= construct-expr
  let proof = def (quote reduce-sound) (vArg expr-resultType ∷ [])
  let solution = def (quote ι⁻¹[_]_) (vArg proof ∷ vArg partial-solution ∷ [])
  debugPrint "vtac" 5 (strErr "↑ macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  ↑ι⟨_⟩_ : ℕ → Term → Term → TC ⊤
  ↑ι⟨ n ⟩ term = weakenι-macro n term
