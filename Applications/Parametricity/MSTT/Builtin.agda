module Applications.Parametricity.MSTT.Builtin where

open import Data.String hiding (Left; Right)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Applications.Parametricity.MSTT.TCMonad


record RelatedTypes : Set₁ where
  field
    Left : Set
    Right : Set
    Relation : REL Left Right 0ℓ

open RelatedTypes public

record BuiltinTypes : Set₁ where
  field
    Code : Set
    show-code : Code → String
    _≟code_ : (c d : Code) → TCM (c ≡ d)
    interpret-code : Code → RelatedTypes

  CodeLeft : Code → Set
  CodeLeft = Left ∘ interpret-code

  CodeRight : Code → Set
  CodeRight = Right ∘ interpret-code

  CodeRelation : (c : Code) → REL (CodeLeft c) (CodeRight c) 0ℓ
  CodeRelation = Relation ∘ interpret-code
