module Experimental.LogicalFramework.Proof.CheckingMonad where

open import Data.String
open import Relation.Nullary as Ag using (Dec; yes; no)


data PCM (A : Set) : Set where
  ok : A → PCM A
  error : String → PCM A

_>>=_ : ∀ {A B} → PCM A → (A → PCM B) → PCM B
ok a    >>= f = f a
error x >>= f = error x

_>>_ : ∀ {A B} → PCM A → PCM B → PCM B
ok x    >> b = b
error x >> b = error x

from-dec : ∀ {A} → Dec A → PCM A
from-dec (yes a) = ok a
from-dec (no ¬a) = error "No element of decidable type found."
