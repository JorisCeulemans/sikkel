--------------------------------------------------
-- Some utilities to write the tactics in the other
-- modules of this folder
--------------------------------------------------

module Reflection.Tactic.Util where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; filter)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary
open import Relation.Unary
open import Reflection
open import Reflection.Argument using (unArg)
open import Reflection.TypeChecking.Monad.Syntax


data IsVisible {a} {A : Set a} : Arg A → Set where
  vis : ∀ {r ty} → IsVisible (arg (arg-info visible r) ty)

visible-dec : ∀ {a} {A : Set a} → Decidable (IsVisible {a} {A})
visible-dec (arg (arg-info visible _) _)   = yes vis
visible-dec (arg (arg-info hidden _) _)    = no λ ()
visible-dec (arg (arg-info instance′ _) _) = no λ ()

get-arg : ∀ {ℓ} {A : Set ℓ} → ℕ → List (Arg A) → TC A
get-arg n       []         = typeError (strErr "The requested argument does not exist." ∷ [])
get-arg 0       (x ∷ _)    = return (unArg x)
get-arg (suc n) (_ ∷ args) = get-arg n args

get-visible-arg : ∀ {ℓ} {A : Set ℓ} → ℕ → List (Arg A) → TC A
get-visible-arg n args = get-arg n (filter visible-dec args)

breakTC : ∀ {a} {A : Set a} → (A → TC Bool) → List A → TC (List A × List A)
breakTC p []       = return ([] , [])
breakTC p (x ∷ xs) = p x >>= λ
  { false → (λ (ys , zs) → (x ∷ ys , zs)) <$> breakTC p xs
  ; true  → return ([] , x ∷ xs)
  }
