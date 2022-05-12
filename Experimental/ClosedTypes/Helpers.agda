module Experimental.ClosedTypes.Helpers where

open import Relation.Binary.PropositionalEquality


remove-≡ids : {A : Set} {f g : A → A} →
              (∀ x → f x ≡ x) →
              (∀ x → g x ≡ x) →
              {a b : A} → f a ≡ g b → a ≡ b
remove-≡ids f-id g-id {a} {b} e = trans (sym (f-id a)) (trans e (g-id b))

remove-≡id : {A : Set} {f : A → A} → (∀ x → f x ≡ x) →
             {a b : A} → f a ≡ f b → a ≡ b
remove-≡id f-id = remove-≡ids f-id f-id
