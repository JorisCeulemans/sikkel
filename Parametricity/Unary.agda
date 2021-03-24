--------------------------------------------------
-- An example of representation independence using
-- unary parametricity
--------------------------------------------------

module Parametricity.Unary where

open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Sum hiding ([_,_])
open import Data.Unit
open import Function using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary hiding (_⇒_)

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Types.Instances
open import Modalities
open import Translation
open import Reflection.Naturality.TypeOperations
open import Reflection.Tactic.Lambda
open import Reflection.SubstitutionSequence

private
  variable
    Γ : Ctx 𝟚


--------------------------------------------------
-- Constructing an embedded type in base category 𝟚
-- using an Agda type and a predicate

PrimFromPred : (A : Set) → Pred A 0ℓ → Ty {C = 𝟚} ◇
PrimFromPred A P ⟨ type-obj , _ ⟩ = A
PrimFromPred A P ⟨ pred-obj , _ ⟩ = Σ[ a ∈ A ] P a
PrimFromPred A P ⟪ type-id , _ ⟫ a = a
PrimFromPred A P ⟪ pred-id , _ ⟫ x = x
PrimFromPred A P ⟪ type-pred , _ ⟫ [ a , p ] = a
ty-cong (PrimFromPred A P) refl {eγ = refl} {eγ' = refl} = refl
ty-id (PrimFromPred A P) {x = type-obj} _ = refl
ty-id (PrimFromPred A P) {x = pred-obj} _ = refl
ty-comp (PrimFromPred A P) type-id g refl refl _ = refl
ty-comp (PrimFromPred A P) pred-id g refl refl _ = refl
ty-comp (PrimFromPred A P) type-pred pred-id _ _ _ = refl

FromPred : (A : Set) → Pred A 0ℓ → ClosedType 𝟚
FromPred A P {Γ = Γ} = PrimFromPred A P [ !◇ Γ ]

instance
  frompred-natural : {A : Set} {P : Pred A 0ℓ} → IsClosedNatural (FromPred A P)
  natural-nul {{frompred-natural}} σ = ty-subst-seq-cong (!◇ _ ∷ σ ◼) (!◇ _ ◼) (PrimFromPred _ _) (◇-terminal _ _ _)

from-pred : {A : Set} {P : Pred A 0ℓ} (a : A) → P a → Tm Γ (FromPred A P)
from-pred a p ⟨ type-obj , _ ⟩' = a
from-pred a p ⟨ pred-obj , _ ⟩' = [ a , p ]
Tm.naturality (from-pred a p) type-id _ = refl
Tm.naturality (from-pred a p) pred-id _ = refl
Tm.naturality (from-pred a p) type-pred _ = refl

from-pred1 : {A B : Set} {P : Pred A 0ℓ} {Q : Pred B 0ℓ}
             (f : A → B) → (P ⟨→⟩ Q) f →
             Tm (Γ ,, FromPred A P) (FromPred B Q)
from-pred1 f g ⟨ type-obj , [ _ , a ] ⟩' = f a
from-pred1 f g ⟨ pred-obj , [ _ , [ a , p ] ] ⟩' = [ f a , g p ]
Tm.naturality (from-pred1 f g) type-id refl = refl
Tm.naturality (from-pred1 f g) pred-id refl = refl
Tm.naturality (from-pred1 f g) type-pred refl = refl

from-pred2 : {A : Set} {P : Pred A 0ℓ}
             {B : Set} {Q : Pred B 0ℓ}
             {C : Set} {R : Pred C 0ℓ}
             (f : A → B → C) → (P ⟨→⟩ Q ⟨→⟩ R) f →
             Tm (Γ ,, FromPred A P ⊠ FromPred B Q) (FromPred C R)
from-pred2 f g ⟨ type-obj , [ _ , [ a , b ] ] ⟩' = f a b
from-pred2 f g ⟨ pred-obj , [ _ , [ [ a , p ] , [ b , q ] ] ] ⟩' = [ f a b , g p q ]
Tm.naturality (from-pred2 f g) type-id refl = refl
Tm.naturality (from-pred2 f g) pred-id refl = refl
Tm.naturality (from-pred2 f g) type-pred refl = refl


--------------------------------------------------
-- Example: types representing booleans

record BoolStructure (B : ClosedType 𝟚) {{_ : IsClosedNatural B}} : Set₁ where
  field
    prim-and : Tm (Γ ,, B ⊠ B) B
    prim-not : Tm (Γ ,, B) B

  and : Tm Γ (B ⊠ B ⇛ B)
  and = lamι (B ⊠ B) prim-and
  
  not : Tm Γ (B ⇛ B)
  not = lamι B prim-not

open BoolStructure {{...}}

or : (B : ClosedType 𝟚) {{_ : IsClosedNatural B}} {{_ : BoolStructure B}} → Tm Γ (B ⇛ B ⇛ B)
or B = lamι[ "b1" ∈ B ] lamι[ "b2" ∈ B ] not $ (and $ pair (not $ varι "b1") (not $ varι "b2"))

-- Representing booleans as natural numbers (0 = false, 1 = true)
data IsBit : Pred ℕ 0ℓ where
  0-bit : IsBit 0
  1-bit : IsBit 1

PrimBinaryBool : Ty {C = 𝟚} ◇
PrimBinaryBool = PrimFromPred ℕ IsBit

BinaryBool : ClosedType 𝟚
BinaryBool = FromPred ℕ IsBit

instance
  binarybool-is-bool : BoolStructure BinaryBool
  prim-and {{binarybool-is-bool}} = from-pred2 _⊓_ ⊓-preserves-bitness
    where
      ⊓-preserves-bitness : (IsBit ⟨→⟩ IsBit ⟨→⟩ IsBit) _⊓_
      ⊓-preserves-bitness 0-bit _     = 0-bit
      ⊓-preserves-bitness 1-bit 0-bit = 0-bit
      ⊓-preserves-bitness 1-bit 1-bit = 1-bit
  prim-not {{binarybool-is-bool}} = from-pred1 (1 ∸_) 1∸-preserves-bitness
    where
      1∸-preserves-bitness : (IsBit ⟨→⟩ IsBit) (1 ∸_)
      1∸-preserves-bitness 0-bit = 1-bit
      1∸-preserves-bitness 1-bit = 0-bit

⊎-trans : {A : Set} {x y z w : A} → x ≡ y → y ≡ z ⊎ y ≡ w → x ≡ z ⊎ x ≡ w
⊎-trans e = Data.Sum.map (trans e) (trans e)

module _ (b : Tm ◇ BinaryBool) where
  translate-b : ℕ
  translate-b = b ⟨ type-obj , _ ⟩'

  type-pred-result : (x : PrimBinaryBool ⟨ pred-obj , _ ⟩) →
                     PrimBinaryBool ⟪ type-pred , refl ⟫ x ≡ 0 ⊎ PrimBinaryBool ⟪ type-pred , refl ⟫ x ≡ 1
  type-pred-result [ .0 , 0-bit ] = inj₁ refl
  type-pred-result [ .1 , 1-bit ] = inj₂ refl

  translated-binary-is-0-or-1 : translate-b ≡ 0 ⊎ translate-b ≡ 1
  translated-binary-is-0-or-1 = ⊎-trans (sym (Tm.naturality b type-pred refl)) (type-pred-result (b ⟨ pred-obj , _ ⟩'))

  translated-binary-is-bit : IsBit translate-b
  translated-binary-is-bit with b ⟨ pred-obj , _ ⟩' | Tm.naturality b type-pred refl
  translated-binary-is-bit | [ _ , p ] | refl = p


--------------------------------------------------
-- Definition of a modality from 𝟚 to ★.

always-false : Ctx ★ → Ctx 𝟚
always-false Γ ⟨ type-obj ⟩ = Γ ⟨ tt ⟩
always-false Γ ⟨ pred-obj ⟩ = ⊥
always-false Γ ⟪ type-id ⟫ γ = γ
always-false Γ ⟪ pred-id ⟫ x = x
always-false Γ ⟪ type-pred ⟫ x = ⊥-elim x
ctx-id (always-false Γ) {x = type-obj} _ = refl
ctx-comp (always-false Γ) type-id g _ = refl
ctx-comp (always-false Γ) pred-id g _ = refl
ctx-comp (always-false Γ) type-pred pred-id _ = refl

always-false-subst : {Δ : Ctx ★} {Γ : Ctx ★} → Δ ⇒ Γ → always-false Δ ⇒ always-false Γ
func (always-false-subst σ) {x = type-obj} = func σ
func (always-false-subst σ) {x = pred-obj} = ⊥-elim
_⇒_.naturality (always-false-subst σ) {f = type-id} _ = refl

always-false-subst-id : {Γ : Ctx ★} → always-false-subst (id-subst Γ) ≅ˢ id-subst (always-false Γ)
eq always-false-subst-id {x = type-obj} _ = refl

always-false-subst-⊚ : {Δ : Ctx ★} {Γ : Ctx ★} {Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                       always-false-subst (σ ⊚ τ) ≅ˢ always-false-subst σ ⊚ always-false-subst τ
eq (always-false-subst-⊚ σ τ) {x = type-obj} _ = refl

forget : {Γ : Ctx ★} → Ty (always-false Γ) → Ty Γ
forget T ⟨ tt , γ ⟩ = T ⟨ type-obj , γ ⟩
forget {Γ = Γ} T ⟪ tt , eγ ⟫ t = T ⟪ type-id , trans (sym (ctx-id Γ _ )) eγ ⟫ t
ty-cong (forget T) refl {eγ = refl} {eγ' = refl} = refl
ty-id (forget T) t = trans (ty-cong T refl) (ty-id T t)
ty-comp (forget T) _ _ _ _ t = sym (ty-cong-2-1 T refl)

module _ {Γ : Ctx ★} {T : Ty (always-false Γ)} where
  forget-intro : Tm (always-false Γ) T → Tm Γ (forget T)
  forget-intro t ⟨ tt , γ ⟩' = t ⟨ type-obj , γ ⟩'
  Tm.naturality (forget-intro t) tt _ = Tm.naturality t type-id _

  forget-elim : Tm Γ (forget T) → Tm (always-false Γ) T
  forget-elim t ⟨ type-obj , γ ⟩' = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-elim t) type-id eγ = trans (ty-cong T refl) (Tm.naturality t tt (trans (ctx-id Γ _) eγ))

module _ {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) {T : Ty (always-false Γ)} where
  forget-natural : (forget T) [ σ ] ≅ᵗʸ forget (T [ always-false-subst σ ])
  func (from forget-natural) = id
  CwF-Structure.naturality (from forget-natural) _ = ty-cong T refl
  func (to forget-natural) = id
  CwF-Structure.naturality (to forget-natural) _ = ty-cong T refl
  eq (isoˡ forget-natural) _ = refl
  eq (isoʳ forget-natural) _ = refl

  forget-intro-natural : (t : Tm (always-false Γ) T) →
                         forget-intro t [ σ ]' ≅ᵗᵐ ι[ forget-natural ] forget-intro (t [ always-false-subst σ ]')
  eq (forget-intro-natural t) _ = refl

  forget-elim-natural : (t : Tm Γ (forget T)) →
                        forget-elim t [ always-false-subst σ ]' ≅ᵗᵐ forget-elim (ι⁻¹[ forget-natural ] (t [ σ ]'))
  eq (forget-elim-natural t) {x = type-obj} _ = refl

forget-cong : {Γ : Ctx ★} {T : Ty (always-false Γ)} {T' : Ty (always-false Γ)} →
              T ≅ᵗʸ T' → forget T ≅ᵗʸ forget T'
func (from (forget-cong T=T')) = func (from T=T')
CwF-Structure.naturality (from (forget-cong T=T')) = CwF-Structure.naturality (from T=T')
func (to (forget-cong T=T')) = func (to T=T')
CwF-Structure.naturality (to (forget-cong T=T')) = CwF-Structure.naturality (to T=T')
eq (isoˡ (forget-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-cong T=T')) = eq (isoʳ T=T')

module _ {Γ : Ctx ★} {T : Ty (always-false Γ)} where
  forget-intro-cong : {t t' : Tm (always-false Γ) T} → t ≅ᵗᵐ t' → forget-intro t ≅ᵗᵐ forget-intro t'
  eq (forget-intro-cong t=t') γ = eq t=t' γ

  forget-elim-cong : {t t' : Tm Γ (forget T)} → t ≅ᵗᵐ t' → forget-elim t ≅ᵗᵐ forget-elim t'
  eq (forget-elim-cong t=t') {x = type-obj} γ = eq t=t' γ

  forget-β : (t : Tm (always-false Γ) T) → forget-elim (forget-intro t) ≅ᵗᵐ t
  eq (forget-β t) {x = type-obj} _ = refl

  forget-η : (t : Tm Γ (forget T)) → forget-intro (forget-elim t) ≅ᵗᵐ t
  eq (forget-η t) _ = refl

instance
  always-false-functor : IsCtxFunctor always-false
  ctx-map {{always-false-functor}} = always-false-subst
  ctx-map-id {{always-false-functor}} = always-false-subst-id
  ctx-map-⊚ {{always-false-functor}} = always-false-subst-⊚

  forget-unarynat : IsUnaryNatural forget
  natural-un {{forget-unarynat}} = forget-natural
  cong-un {{forget-unarynat}} = forget-cong

forget-mod : Modality 𝟚 ★
forget-mod = record
   { ctx-op = always-false
   ; mod = forget
   ; mod-cong = forget-cong
   ; mod-natural = forget-natural
   ; mod-intro = forget-intro
   ; mod-intro-cong = forget-intro-cong
   ; mod-intro-natural = forget-intro-natural
   ; mod-elim = forget-elim
   ; mod-elim-cong = forget-elim-cong
   ; mod-elim-natural = forget-elim-natural
   ; mod-β = forget-β
   ; mod-η = forget-η
   }


--------------------------------------------------
-- Continuing the example of binary numbers representing booleans

binary-or : Tm Γ (BinaryBool ⇛ BinaryBool ⇛ BinaryBool)
binary-or = or BinaryBool

binary-or★ : {Γ : Ctx ★} → Tm Γ (forget BinaryBool ⇛ forget BinaryBool ⇛ forget BinaryBool)
binary-or★ = lamι[ "x" ∈ forget BinaryBool ] lamι[ "y" ∈ forget BinaryBool ]
             forget-intro binary-or ⊛⟨ forget-mod ⟩ varι "x" ⊛⟨ forget-mod ⟩ varι "y"

instance
  forget-pred : {A : Set} {P : Pred A 0ℓ} → Translatable (forget (FromPred A P))
  Translatable.translated-type (forget-pred {A = A}) = A
  Translatable.translate-term forget-pred t = t ⟨ tt , tt ⟩'
  Translatable.translate-back forget-pred a = MkTm (λ _ _ → a) (λ _ _ → refl)

binary-or-agda : ℕ → ℕ → ℕ
binary-or-agda = translate-term binary-or★

translate-result : (IsBit ⟨→⟩ IsBit ⟨→⟩ IsBit) binary-or-agda
translate-result {m} x {n} y = proj₂ ((binary-or {Γ = ◇} €⟨ pred-obj , tt ⟩ [ m , x ]) $⟨ pred-id , refl ⟩ [ n , y ])
