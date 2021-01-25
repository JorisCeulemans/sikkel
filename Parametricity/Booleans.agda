{-# OPTIONS --omega-in-omega #-}

module Parametricity.Booleans where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Sum
open import Function using (id)
open import Level using (Level; Setω; 0ℓ)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Reflection.Naturality
open import Reflection.Naturality.Instances
open import Reflection.Tactic.Lambda
open import Reflection.SubstitutionSequence

private
  variable
    ℓ : Level
    Γ : Ctx 𝟚 ℓ


{-
discard-pred-ty : Ty {C = 𝟚} ◇ ℓ → Ty {C = ★} ◇ ℓ
type (discard-pred-ty T) tt tt = T ⟨ type-obj , tt ⟩
morph (discard-pred-ty T) tt _ = id
morph-cong (discard-pred-ty T) {f = tt} _ = refl
morph-id (discard-pred-ty T) _ = refl
morph-comp (discard-pred-ty T) _ _ _ _ _ = refl

discard-pred-tm : {T : Ty ◇ ℓ} → Tm ◇ T → Tm ◇ (discard-pred-ty T)
term (discard-pred-tm t) tt tt = t ⟨ type-obj , tt ⟩'
Tm.naturality (discard-pred-tm t) _ _ = refl
-}

record BoolStructure (B : NullaryTypeOp 𝟚 ℓ) : Setω where
  field
    and : Tm Γ (B ⊠ B ⇛ B)
    not : Tm Γ (B ⇛ B)
open BoolStructure {{...}}

or : (B : NullaryTypeOp 𝟚 ℓ) {{_ : IsNullaryNatural B}} {{_ : BoolStructure B}} → Tm Γ (B ⊠ B ⇛ B)
or B = nlamι "bs" (B ⊠ B) (not $ (and $ pair (not $ fst (nvarι "bs")) (not $ snd (nvarι "bs"))))

PrimBinaryBool : Ty {C = 𝟚} ◇ 0ℓ
type PrimBinaryBool type-obj _ = ℕ
type PrimBinaryBool pred-obj _ = Bool
morph PrimBinaryBool type-id _ = id
morph PrimBinaryBool pred-id _ = id
morph PrimBinaryBool type-pred _ false = 0
morph PrimBinaryBool type-pred _ true  = 1
morph-cong PrimBinaryBool {f = type-id} refl = refl
morph-cong PrimBinaryBool {f = pred-id} refl = refl
morph-cong PrimBinaryBool {f = type-pred} refl {t = false} = refl
morph-cong PrimBinaryBool {f = type-pred} refl {t = true } = refl
morph-id PrimBinaryBool {x = type-obj} _ = refl
morph-id PrimBinaryBool {x = pred-obj} _ = refl
morph-comp PrimBinaryBool type-id g _ _ _ = morph-cong PrimBinaryBool {f = g} refl
morph-comp PrimBinaryBool pred-id g _ _ _ = morph-cong PrimBinaryBool {f = g} refl
morph-comp PrimBinaryBool type-pred pred-id _ _ t = morph-cong PrimBinaryBool {f = type-pred} refl {t = t}

BinaryBool : NullaryTypeOp 𝟚 0ℓ
BinaryBool {Γ = Γ} = PrimBinaryBool [ !◇ Γ ]

instance
  binarybool-natural : IsNullaryNatural BinaryBool
  natural-nul {{binarybool-natural}} σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) PrimBinaryBool (◇-terminal _ _ _)
  
  binarybool-is-bool : BoolStructure BinaryBool
  term (and ⦃ binarybool-is-bool ⦄) type-obj γ $⟨ type-id , refl ⟩ [ m , n ] = m ⊓ n
  PresheafFunc.naturality (term (and ⦃ binarybool-is-bool ⦄) type-obj γ) {ρ-xy = type-id} {ρ-yz = type-id} refl refl _ = {!!}
  term (and ⦃ binarybool-is-bool ⦄) pred-obj γ $⟨ pred-id , refl ⟩ [ b1 , b2 ] = b1 ∧ b2
  term (and ⦃ binarybool-is-bool ⦄) pred-obj γ $⟨ type-pred , refl ⟩ [ m , n ] = m ⊓ n
  PresheafFunc.naturality (term (and ⦃ binarybool-is-bool ⦄) pred-obj γ) = {!!}
  Tm.naturality (and ⦃ binarybool-is-bool ⦄) f eγ = to-pshfun-eq {!!}
  not {{binarybool-is-bool}} = {!!}


⊎-trans : {A : Set ℓ} {x y z w : A} → x ≡ y → y ≡ z ⊎ y ≡ w → x ≡ z ⊎ x ≡ w
⊎-trans e = Data.Sum.map (trans e) (trans e)

module _ (b : Tm ◇ BinaryBool) where
  translate-b : ℕ
  translate-b = b ⟨ type-obj , _ ⟩'

  type-pred-result : (x : PrimBinaryBool ⟨ pred-obj , _ ⟩) →
                     PrimBinaryBool ⟪ type-pred , refl ⟫ x ≡ 0 ⊎ PrimBinaryBool ⟪ type-pred , refl ⟫ x ≡ 1
  type-pred-result false = inj₁ refl
  type-pred-result true  = inj₂ refl

  result : translate-b ≡ 0 ⊎ translate-b ≡ 1
  result = ⊎-trans (sym (Tm.naturality b type-pred refl)) (type-pred-result (b ⟨ pred-obj , _ ⟩'))
