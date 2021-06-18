--------------------------------------------------
-- Definition of macros that enable working with
-- variables and weakening (see CwF-Structure.Telescopes)
-- without having to specify the telescope.
--------------------------------------------------

module Experimental.UntypedNaturalitySolver.Tactic.Telescopes where

open import Data.Bool hiding (_<?_)
open import Data.Fin using (#_)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.String hiding (_<?_)
open import Data.Unit
open import Reflection hiding (var)
open import Reflection.TypeChecking.Monad.Syntax
open import Relation.Nullary.Decidable using (⌊_⌋)

open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import CwF-Structure.Telescopes hiding (_++_)
open import Experimental.UntypedNaturalitySolver.Solver renaming (reduce to nat-reduce) hiding (⊤)
open import Experimental.UntypedNaturalitySolver.Tactic.ConstructExpression
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

-- ctx-to-telescope takes a value of type Ctx C ℓ and transforms it into a telescope
-- If a context is of the form Γ ,, T then T is added to the telescope
-- and ctx-to-telescope is called recursively on Γ. Otherwise the process
-- stops and ctx-to-telescope returns an empty telescope.
{-# TERMINATING #-}
ctx-to-telescope : Term → TC Term
ctx-to-telescope (def (quote _,,_) args) = do
  ctx ← get-visible-arg 0 args
  ty ← get-visible-arg 1 args
  (λ telescope → con (quote Telescope._∷_) (vArg telescope ∷ vArg ty ∷ [])) <$> ctx-to-telescope ctx
ctx-to-telescope (def (quote _,,_∈_) args) = do
  ctx ← get-visible-arg 0 args
  ty ← get-visible-arg 2 args
  (λ telescope → con (quote Telescope._∷_) (vArg telescope ∷ vArg ty ∷ [])) <$> ctx-to-telescope ctx
ctx-to-telescope (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in ctx-to-telescope." ∷ []) >>
                                 blockOnMeta m
ctx-to-telescope _ = return (con (quote Telescope.[]) [])


--------------------------------------------------
-- Definition of the macro db-var that allows to refer
-- to variables in context by de Bruijn indices.
-- It turns a context into a telescope and applies prim-var.

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

db-var-macro : Term → Term → TC ⊤
db-var-macro x hole = do
  solution ← construct-var-solution x hole
  debugPrint "vtac" 5 (strErr "var macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  db-var : Term → Term → TC ⊤
  db-var = db-var-macro


-------------------------------------------------
-- Variable (de Bruijn index) macro that automatically performs naturality reduction on its type

db-varι-macro : Term → Term → TC ⊤
db-varι-macro x hole = do
  partialSolution ← construct-var-solution x hole
  expr-resultType ← inferType partialSolution >>= get-term-type >>= construct-expr
  let proof = def (quote reduce-sound) (vArg expr-resultType ∷ [])
  let solution = def (quote ι⁻¹[_]_) (vArg proof ∷ vArg partialSolution ∷ [])
  debugPrint "vtac" 5 (strErr "varι macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  db-varι : Term → Term → TC ⊤
  db-varι = db-varι-macro


--------------------------------------------------
-- Variable macro that allows to name variables using strings.

{-# TERMINATING #-}
get-deBruijn-index : Term → String → TC ℕ
get-deBruijn-index (def (quote _,,_) args) v = do
  ctx ← get-visible-arg 0 args
  i ← get-deBruijn-index ctx v
  return (1 + i)
get-deBruijn-index (def (quote _,,_∈_) args) v = do
  w ← get-visible-arg 1 args >>= unquoteTC -- name of the last variable added to the context
  if (v == w)
    then return 0
    else do
      ctx ← get-visible-arg 0 args
      i ← get-deBruijn-index ctx v
      return (1 + i)
get-deBruijn-index (meta m args) v = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in get-deBruijn-index." ∷ []) >>
                                     blockOnMeta m
get-deBruijn-index _ v = typeError (strErr ("Could not find a variable with name " ++ v) ∷ [])

var-macro : String → Term → TC ⊤
var-macro v hole = do
  goal ← inferType hole
  ctx ← get-ctx goal
  i ← get-deBruijn-index ctx v >>= quoteTC
  db-var-macro i hole

varι-macro : String → Term → TC ⊤
varι-macro v hole = do
  goal ← inferType hole
  ctx ← get-ctx goal
  i ← get-deBruijn-index ctx v >>= quoteTC
  db-varι-macro i hole

macro
  var = var-macro
  varι = varι-macro


-------------------------------------------------
-- Definition of a macro that performs weakening of terms
-- and infers the telescope itself from the current context.

bounded-ctx-to-telescope : ℕ → Term → TC Term
bounded-ctx-to-telescope 0       _ = return (con (quote Telescope.[]) [])
bounded-ctx-to-telescope (suc n) (def (quote _,,_) args) = do
  ctx ← get-visible-arg 0 args
  ty ← get-visible-arg 1 args
  (λ telescope → con (quote Telescope._∷_) (vArg telescope ∷ vArg ty ∷ [])) <$> bounded-ctx-to-telescope n ctx
bounded-ctx-to-telescope (suc n) (def (quote _,,_∈_) args) = do
  ctx ← get-visible-arg 0 args
  ty ← get-visible-arg 2 args
  (λ telescope → con (quote Telescope._∷_) (vArg telescope ∷ vArg ty ∷ [])) <$> bounded-ctx-to-telescope n ctx
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
