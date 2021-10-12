--------------------------------------------------
-- The FromRel type constructor will allow to
-- interpret a number of triples, consisting of two
-- Agda types and a relation, as MSTT types at mode ⋀.
-- To retain decidable equivalence checking, such triples
-- are encoded by a universe defined in this file.
--------------------------------------------------

module Applications.Parametricity.MSTT.TypeExtension.RelExtension where

open import Data.String hiding (Left; Right)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import MSTT.TCMonad


record RelatedTypes : Set₁ where
  field
    Left : Set
    Right : Set
    Relation : REL Left Right 0ℓ

open RelatedTypes public

record RelExt : Set₁ where
  field
    RelCode : Set
    show-code : RelCode → String
    _≟code_ : (c d : RelCode) → TCM (c ≡ d)
    interpret-code : RelCode → RelatedTypes

  CodeLeft : RelCode → Set
  CodeLeft = Left ∘ interpret-code

  CodeRight : RelCode → Set
  CodeRight = Right ∘ interpret-code

  CodeRelation : (c : RelCode) → REL (CodeLeft c) (CodeRight c) 0ℓ
  CodeRelation = Relation ∘ interpret-code
