-- Definition of 2 functions that should be in the standard library but currently are not.

module Experimental.LogicalFramework.MSTT.Normalization.Helpers where

open import Data.Maybe
open import Function


infixl 4 _<$>_ _<*>_
_<$>_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → Maybe A → Maybe B
f <$> ma = map f ma

_<*>_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → Maybe (A → B) → Maybe A → Maybe B
_<*>_ = maybe map (const nothing)
