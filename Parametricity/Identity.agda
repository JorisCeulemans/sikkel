module Parametricity.Identity where

open import Data.Unit
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Translation

private
  variable
    ℓ : Level


discard-pred-ty : Ty {C = 𝟚} ◇ ℓ → Ty {C = ★} ◇ ℓ
type (discard-pred-ty T) tt tt = T ⟨ type-obj , tt ⟩
morph (discard-pred-ty T) tt _ = id
morph-cong (discard-pred-ty T) {f = tt} _ = refl
morph-id (discard-pred-ty T) _ = refl
morph-comp (discard-pred-ty T) _ _ _ _ _ = refl

discard-pred-tm : {T : Ty ◇ ℓ} → Tm ◇ T → Tm ◇ (discard-pred-ty T)
term (discard-pred-tm t) tt tt = t ⟨ type-obj , tt ⟩'
Tm.naturality (discard-pred-tm t) _ _ = refl

{-
module _ (f : (T : Ty {C = 𝟚} ◇ ℓ) → Tm ◇ (T ⇛ T)) (A : Set ℓ) where
  fA : A → A
  fA = f (Discr A) €⟨ type-obj , tt ⟩_
-}

module _ (f : (T : Ty {C = 𝟚} ◇ ℓ) → Tm ◇ (T ⇛ T)) (A : Set ℓ) (a : A) where
  Ta : Ty {C = 𝟚} ◇ ℓ
  type Ta type-obj tt = A
  type Ta pred-obj tt = Lift ℓ ⊤
  morph Ta type-id _ = id
  morph Ta pred-id _ = id
  morph Ta type-pred _ = const a
  morph-cong Ta {f = type-id} refl = refl
  morph-cong Ta {f = pred-id} refl = refl
  morph-cong Ta {f = type-pred} refl = refl
  morph-id Ta {x = type-obj} _ = refl
  morph-id Ta {x = pred-obj} _ = refl
  morph-comp Ta type-id g refl refl _ = refl
  morph-comp Ta pred-id g refl refl _ = refl
  morph-comp Ta type-pred pred-id refl refl _ = refl

  fA : A → A
  fA = f Ta €⟨ type-obj , tt ⟩_

  fAa=a : fA a ≡ a
  fAa=a = sym (€-natural (f Ta) type-pred refl (lift tt))
