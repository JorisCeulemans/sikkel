module Reflection.Util where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Reflection
open import Reflection.Argument using (unArg)
open import Reflection.TypeChecking.Monad.Syntax

getArg : ∀ {ℓ} {A : Set ℓ} → ℕ → List (Arg A) → TC A
getArg n []               = typeError (strErr "The requested argument does not exist." ∷ [])
getArg 0 (x ∷ _)          = return (unArg x)
getArg (suc n) (_ ∷ args) = getArg n args

getVisibleArg : ∀ {ℓ} {A : Set ℓ} → ℕ → List (Arg A) → TC A
getVisibleArg n       []              = typeError (strErr "The requested visible argument does not exist." ∷ [])
getVisibleArg 0       (vArg e ∷ _)    = return e
getVisibleArg (suc n) (vArg _ ∷ args) = getVisibleArg n args
getVisibleArg n       (_ ∷ args)      = getVisibleArg n args

breakTC : ∀ {a} {A : Set a} → (A → TC Bool) → List A → TC (List A × List A)
breakTC p []       = return ([] , [])
breakTC p (x ∷ xs) = p x >>= λ
  { false → (λ (ys , zs) → (x ∷ ys , zs)) <$> breakTC p xs
  ; true  → return ([] , x ∷ xs)
  }

is-visible : ∀ {a} {A : Set a} → Arg A → Bool
is-visible (arg (arg-info visible _) _) = true
is-visible (arg (arg-info hidden _) _) = false
is-visible (arg (arg-info instance′ _) _) = false
