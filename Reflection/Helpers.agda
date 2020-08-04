{-# OPTIONS --omega-in-omega #-}

module Reflection.Helpers where

open import Level
open import Relation.Binary.PropositionalEquality

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  instance refl : x ≡ω x

ω-transp : ∀ {ℓ} {A : Set ℓ} (P : A → Setω) {a b : A} →
           a ≡ b → P a → P b
ω-transp P refl p = p
