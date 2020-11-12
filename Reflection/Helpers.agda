{-# OPTIONS --without-K --omega-in-omega #-}

-- Note that we use the option omega-in-omega in order to define
-- an inductive data type in Setω and to pattern match on it (which
-- is not possible in Agda 2.6.1 without this option). This code should
-- typecheck without this option in Agda 2.6.2 once released (tested with
-- the development version on July 10, 2020).

module Reflection.Helpers where

open import Level
open import Relation.Binary.PropositionalEquality

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  instance refl : x ≡ω x

ω-transp : ∀ {ℓ} {A : Set ℓ} (P : A → Setω) {a b : A} →
           a ≡ b → P a → P b
ω-transp P refl p = p
