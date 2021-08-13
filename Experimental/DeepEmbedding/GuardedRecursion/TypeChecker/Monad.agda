--------------------------------------------------
-- The Type Checking Monad
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Monad where

open import Category.Monad
open import Data.String
open import Data.Sum hiding (map)
import Data.Sum.Categorical.Left as Sum
open import Level


-- The type checking monad currently only allows for simple strings as error messages.
TCM : Set → Set
TCM A = String ⊎ A

pattern type-error x = inj₁ x
pattern ok x = inj₂ x

map : ∀ {A B} → (A → B) → TCM A → TCM B
map = Data.Sum.map₂

open RawMonad (Sum.monad String 0ℓ) public

tcm-elim : ∀ {A} {ℓ} {B : Set ℓ} → (String → B) → (A → B) → TCM A → B
tcm-elim = [_,_]′
