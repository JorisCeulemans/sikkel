{-# OPTIONS --omega-in-omega #-}

module Reflection.Helpers where

open import Level

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  instance refl : x ≡ω x
