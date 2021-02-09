--------------------------------------------------
-- Reflecting a (semantic) type as an expression
-- using nullary, unary and binary natural operators.
--------------------------------------------------

module Reflection.Tactic.ConstructExpression where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; #_; toℕ)
open import Data.List using (List; []; _∷_; filter)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Reflection
open import Reflection.Argument using (_⟨∷⟩_; unArg)

open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import CwF-Structure.Telescopes
open import Reflection.Naturality renaming (reduce to nat-reduce)
open import Reflection.Tactic.Util


is-arg-semtype : Arg Term → TC Bool
is-arg-semtype a = inferType (unArg a) >>= λ
  { (def (quote Ty) _) → return true
  ; _ → return false
  }

get-term-type : Type → TC Term
get-term-type (def (quote Tm) args) = get-visible-arg 1 args
get-term-type (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in get-term-type." ∷ []) >>
                              blockOnMeta m
get-term-type _ = typeError (strErr "This tactic can only be used to construct a term." ∷ [])

telescope-lookup : Term → {n : ℕ} → Fin n → TC Term
telescope-lookup (con (quote Telescope.[])  args) i       = typeError (strErr "The requested variable does not exist." ∷ [])
telescope-lookup (con (quote Telescope._∷_) args) zero    = get-visible-arg 1 args
telescope-lookup (con (quote Telescope._∷_) args) (suc i) = get-visible-arg 0 args >>= λ telescope → telescope-lookup telescope i
telescope-lookup _ i = typeError (strErr "telescope-lookup is not called with a telescope." ∷ [])
{-
weaken-var-expr : Term → {n : ℕ} → Fin n → Term
weaken-var-expr expr zero    = con (quote sub) (expr ⟨∷⟩ def (quote π) [] ⟨∷⟩ [])
weaken-var-expr expr (suc i) = con (quote sub) (weaken-var-expr expr i ⟨∷⟩ def (quote π) [] ⟨∷⟩ [])
-}
weaken-expr : Term → ℕ → Term
weaken-expr expr zero    = expr
weaken-expr expr (suc n) = con (quote sub) (weaken-expr expr n ⟨∷⟩ def (quote π) [] ⟨∷⟩ [])

default-construct-expr : (List (Arg Term) → Term) → List (Arg Term) → TC Term
construct-expr : Term → TC Term

-- Construct expressions for defined terms and Agda variables
default-construct-expr operation args = breakTC is-arg-semtype (filter visible-dec args) >>= λ
  { (others , []) → return (con (quote nul) (vArg (operation others) ∷ []))  -- Nullary type operation.
  ; (others , (ty1 ⟨∷⟩ [])) → do  -- Unary type operation.
      ty1-exp ← construct-expr ty1
      return (con (quote un) (vArg (operation others) ∷ vArg ty1-exp ∷ []))
  ; (others , (ty1 ⟨∷⟩ ty2 ⟨∷⟩ [])) → do  -- Binary type operation.
      ty1-exp ← construct-expr ty1
      ty2-exp ← construct-expr ty2
      return (con (quote bin) (vArg (operation others) ∷ vArg ty1-exp ∷ vArg ty2-exp ∷ []))
  ; _ → typeError (strErr "No type operator recognized." ∷ [])
  }

{-# TERMINATING #-}
construct-expr (def (quote ⟦_⟧exp) args) = get-visible-arg 0 args
construct-expr (def (quote var-type) args) = do  -- Look up the type in the telescope.
  t-telescope ← get-visible-arg 0 args
  len-telescope ← get-arg 3 args >>= unquoteTC
  var-num ← get-visible-arg 1 args >>= unquoteTC  -- var-num is the de Bruijn index of the variable.
  t-type ← telescope-lookup t-telescope {len-telescope} var-num
  expr-type ← construct-expr t-type
  return (weaken-expr expr-type (suc (toℕ var-num)))
construct-expr (def (quote weaken-type) args) = do  -- The type is given as argument 1 to weaken-type (but sufficiently π substitutions must still be applied).
  expr-not-weakened-type ← get-visible-arg 1 args >>= construct-expr
  weaken-nr ← get-arg 4 args >>= unquoteTC  -- Number of times π is applied
  return (weaken-expr expr-not-weakened-type weaken-nr)
construct-expr (def (quote _[_]) args) = breakTC is-arg-semtype args >>= λ
  { (_ , (ty ⟨∷⟩ subst ⟨∷⟩ [])) → do
      ty-exp ← construct-expr ty
      return (con (quote sub) (vArg ty-exp ∷ vArg subst ∷ []))
  ; _ → typeError (strErr "Illegal substitution." ∷ [])
  }
construct-expr (def op args) = default-construct-expr (def op) args
construct-expr (var x args) = default-construct-expr (var x) args
construct-expr (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in construct-expr." ∷ []) >>
                               blockOnMeta m
construct-expr ty = typeError (strErr "The naturality tactic does not work for the type" ∷ termErr ty ∷ [])

