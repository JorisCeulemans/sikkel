{-# OPTIONS --omega-in-omega #-}

module Parametricity.Unary where

--open import Data.Bool using (Bool; true; false; _∧_) renaming (not to b-not)
open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Sum hiding ([_,_])
open import Function using (id)
open import Level using (Level; Setω; 0ℓ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary

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
    ℓ ℓ' : Level
    Γ : Ctx 𝟚 ℓ


PrimFromPred : (A : Set ℓ) → Pred A ℓ → Ty {C = 𝟚} ◇ ℓ
type (PrimFromPred A P) type-obj _ = A
type (PrimFromPred A P) pred-obj _ = Σ[ a ∈ A ] P a
morph (PrimFromPred A P) type-id _ = id
morph (PrimFromPred A P) pred-id _ = id
morph (PrimFromPred A P) type-pred _ = proj₁
morph-cong (PrimFromPred A P) refl {eγ = refl} {eγ' = refl} = refl
morph-id (PrimFromPred A P) {x = type-obj} _ = refl
morph-id (PrimFromPred A P) {x = pred-obj} _ = refl
morph-comp (PrimFromPred A P) type-id g refl refl _ = refl
morph-comp (PrimFromPred A P) pred-id g refl refl _ = refl
morph-comp (PrimFromPred A P) type-pred pred-id _ _ _ = refl

FromPred : (A : Set ℓ) → Pred A ℓ → NullaryTypeOp 𝟚 ℓ
FromPred A P {Γ = Γ} = PrimFromPred A P [ !◇ Γ ]

instance
  frompred-natural : {A : Set ℓ} {P : Pred A ℓ} → IsNullaryNatural (FromPred A P)
  natural-nul {{frompred-natural}} σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) (PrimFromPred _ _) (◇-terminal _ _ _)

from-pred : {A : Set ℓ} {P : Pred A ℓ} (a : A) → P a → Tm Γ (FromPred A P)
term (from-pred a p) type-obj _ = a
term (from-pred a p) pred-obj _ = [ a , p ]
Tm.naturality (from-pred a p) type-id _ = refl
Tm.naturality (from-pred a p) pred-id _ = refl
Tm.naturality (from-pred a p) type-pred _ = refl

from-pred1 : {A : Set ℓ}  {P : Pred A ℓ}
             {B : Set ℓ'} {Q : Pred B ℓ'}
             (f : A → B) → (P ⟨→⟩ Q) f →
             Tm (Γ ,, FromPred A P) (FromPred B Q)
term (from-pred1 f g) type-obj [ _ , a ] = f a
term (from-pred1 f g) pred-obj [ _ , [ a , p ] ] = [ f a , g p ]
Tm.naturality (from-pred1 f g) type-id refl = refl
Tm.naturality (from-pred1 f g) pred-id refl = refl
Tm.naturality (from-pred1 f g) type-pred refl = refl

from-pred2 : ∀ {ℓa ℓb ℓc}
             {A : Set ℓa} {P : Pred A ℓa}
             {B : Set ℓb} {Q : Pred B ℓb}
             {C : Set ℓc} {R : Pred C ℓc}
             (f : A → B → C) → (P ⟨→⟩ Q ⟨→⟩ R) f →
             Tm (Γ ,, FromPred A P ⊠ FromPred B Q) (FromPred C R)
term (from-pred2 f g) type-obj [ _ , [ a , b ] ] = f a b
term (from-pred2 f g) pred-obj [ _ , [ [ a , p ] , [ b , q ] ] ] = [ f a b , g p q ]
Tm.naturality (from-pred2 f g) type-id refl = refl
Tm.naturality (from-pred2 f g) pred-id refl = refl
Tm.naturality (from-pred2 f g) type-pred refl = refl
             

record BoolStructure (B : NullaryTypeOp 𝟚 ℓ) {{_ : IsNullaryNatural B}} : Setω where
  field
    prim-and : Tm (Γ ,, B ⊠ B) B
    prim-not : Tm (Γ ,, B) B

  and : Tm Γ (B ⊠ B ⇛ B)
  and = lamι (B ⊠ B) prim-and
  
  not : Tm Γ (B ⇛ B)
  not = lamι B prim-not
open BoolStructure {{...}}

or : (B : NullaryTypeOp 𝟚 ℓ) {{_ : IsNullaryNatural B}} {{_ : BoolStructure B}} → Tm Γ (B ⊠ B ⇛ B)
or B = nlamι[ "bs" ∈ B ⊠ B ] not $ (and $ pair (not $ fst (nvarι "bs")) (not $ snd (nvarι "bs")))

data IsBit : Pred ℕ 0ℓ where
  0-bit : IsBit 0
  1-bit : IsBit 1

PrimBinaryBool : Ty {C = 𝟚} ◇ 0ℓ
PrimBinaryBool = PrimFromPred ℕ IsBit

BinaryBool : NullaryTypeOp 𝟚 0ℓ
BinaryBool {Γ = Γ} = FromPred ℕ IsBit

instance
  binarybool-is-bool : BoolStructure BinaryBool
  prim-and {{binarybool-is-bool}} = from-pred2 _⊓_ (λ { 0-bit _ → 0-bit ; 1-bit 0-bit → 0-bit ; 1-bit 1-bit → 1-bit })
  prim-not {{binarybool-is-bool}} = from-pred1 (1 ∸_) (λ { 0-bit → 1-bit ; 1-bit → 0-bit })

⊎-trans : {A : Set ℓ} {x y z w : A} → x ≡ y → y ≡ z ⊎ y ≡ w → x ≡ z ⊎ x ≡ w
⊎-trans e = Data.Sum.map (trans e) (trans e)

module _ (b : Tm ◇ BinaryBool) where
  translate-b : ℕ
  translate-b = b ⟨ type-obj , _ ⟩'

  type-pred-result : (x : PrimBinaryBool ⟨ pred-obj , _ ⟩) →
                     PrimBinaryBool ⟪ type-pred , refl ⟫ x ≡ 0 ⊎ PrimBinaryBool ⟪ type-pred , refl ⟫ x ≡ 1
  type-pred-result [ .0 , 0-bit ] = inj₁ refl
  type-pred-result [ .1 , 1-bit ] = inj₂ refl

  result : translate-b ≡ 0 ⊎ translate-b ≡ 1
  result = ⊎-trans (sym (Tm.naturality b type-pred refl)) (type-pred-result (b ⟨ pred-obj , _ ⟩'))

  result' : IsBit translate-b
  result' with b ⟨ pred-obj , _ ⟩' | Tm.naturality b type-pred refl
  result' | [ _ , p ] | refl = p


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
