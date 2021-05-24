--------------------------------------------------
-- Reflecting a (semantic) type as an untyped expression
-- using nullary, unary and binary natural operators.
--------------------------------------------------

module Reflection.Tactic.NewSolver.ConstructExpression where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; #_; toℕ)
open import Data.List using (List; []; _∷_; filter)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Reflection
open import Reflection.Argument using (_⟨∷⟩_; _⟅∷⟆_; unArg)

open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import CwF-Structure.Telescopes
open import Reflection.Naturality.NewSolver renaming (reduce to nat-reduce)
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

{-# TERMINATING #-}
weaken-expr : Term → Term → Term → TC Term
weaken-expr expr ctx (con (quote Telescope.[]) args)  = return expr
weaken-expr expr ctx tele@(con (quote Telescope._∷_) args) = do
  init-tele ← get-visible-arg 0 args
  partial-result ← weaken-expr expr ctx init-tele
  let result = con (quote sub) (
                 partial-result ⟨∷⟩
                 def (quote _++_) (ctx ⟨∷⟩ tele      ⟨∷⟩ []) ⟨∷⟩
                 def (quote _++_) (ctx ⟨∷⟩ init-tele ⟨∷⟩ []) ⟨∷⟩
                 def (quote π) [] ⟨∷⟩ [])
  return result
weaken-expr expr ctx _ = typeError (strErr "weaken-expr is not called with a telescope." ∷ [])

splitTelescopeAt : ∀ {n} → Fin n → Term → Term → TC (Term × Term)
splitTelescopeAt zero ctx tele = return (def (quote _++_) (ctx ⟨∷⟩ tele ⟨∷⟩ []) , (con (quote Telescope.[]) []))
splitTelescopeAt (suc i) ctx (con (quote Telescope._∷_) args) = do
  init-tele ← get-visible-arg 0 args
  tail-type ← get-visible-arg 1 args
  res-ctx , partial-res-tele ← splitTelescopeAt i ctx init-tele
  return (res-ctx , (con (quote Telescope._∷_) (partial-res-tele ⟨∷⟩ tail-type ⟨∷⟩ [])))
splitTelescopeAt _ ctx _ = typeError (strErr "splitTelescopeAt is not called with a telescope or with an empty telescope." ∷ [])

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
construct-expr (def (quote interp-expr) args) = get-visible-arg 0 args
construct-expr (def (quote var-type) args) = do  -- Look up the type in the telescope.
  t-telescope ← get-visible-arg 0 args
  len-telescope ← get-arg 2 args >>= unquoteTC
  var-num ← get-visible-arg 1 args >>= unquoteTC  -- var-num is the de Bruijn index of the variable.
  expr-type ← telescope-lookup t-telescope {len-telescope} var-num >>= construct-expr
  ctx ← get-arg 1 args
  new-ctx , new-telescope ← splitTelescopeAt (suc var-num) ctx t-telescope
  weaken-expr expr-type new-ctx new-telescope
construct-expr (def (quote weaken-type) args) = do  -- The type is given as argument 1 to weaken-type (but sufficiently π substitutions must still be applied).
  expr-not-weakened-type ← get-visible-arg 1 args >>= construct-expr
  telescope ← get-visible-arg 0 args
  ctx ← get-arg 1 args
  weaken-expr expr-not-weakened-type ctx telescope
construct-expr (def (quote _[_]) args) = case args of λ
  { (_ ⟅∷⟆ ctx-to ⟅∷⟆ ctx-from ⟅∷⟆ ty ⟨∷⟩ subst ⟨∷⟩ []) → do
      ty-exp ← construct-expr ty
      return (con (quote sub) (ty-exp ⟨∷⟩ ctx-from ⟨∷⟩ ctx-to ⟨∷⟩ subst ⟨∷⟩ []))
  ; _ → typeError (strErr "Illegal substitution." ∷ [])
  }
construct-expr (def op args) = default-construct-expr (def op) args
construct-expr (var x args) = default-construct-expr (var x) args
construct-expr (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in construct-expr." ∷ []) >>
                               blockOnMeta m
construct-expr ty = typeError (strErr "The naturality tactic does not work for the type" ∷ termErr ty ∷ [])
