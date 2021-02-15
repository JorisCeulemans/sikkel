{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- An example of representation independence using
-- unary parametricity
--------------------------------------------------

module Parametricity.Unary where

open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Sum hiding ([_,_])
open import Function using (id)
open import Level using (Level; Setω; 0ℓ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary hiding (_⇒_)

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
    ℓ ℓ' ℓ'' : Level
    fℓ : Level → Level
    Γ : Ctx 𝟚 ℓ


--------------------------------------------------
-- Constructing an embedded type in base category 𝟚
-- using an Agda type and a predicate

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

FromPred : (A : Set ℓ) → Pred A ℓ → NullaryTypeOp 𝟚 (λ _ → ℓ)
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


--------------------------------------------------
-- Example: types representing booleans

record BoolStructure (B : NullaryTypeOp 𝟚 fℓ) {{_ : IsNullaryNatural B}} : Setω where
  field
    prim-and : Tm (Γ ,, B ⊠ B) B
    prim-not : Tm (Γ ,, B) B

  and : Tm Γ (B ⊠ B ⇛ B)
  and = lamι (B ⊠ B) prim-and
  
  not : Tm Γ (B ⇛ B)
  not = lamι B prim-not

open BoolStructure {{...}}

or : (B : NullaryTypeOp 𝟚 fℓ) {{_ : IsNullaryNatural B}} {{_ : BoolStructure B}} → Tm Γ (B ⇛ B ⇛ B)
or B = lamι[ "b1" ∈ B ] lamι[ "b2" ∈ B ] not $ (and $ pair (not $ varι "b1") (not $ varι "b2"))

-- Representing booleans as natural numbers (0 = false, 1 = true)
data IsBit : Pred ℕ 0ℓ where
  0-bit : IsBit 0
  1-bit : IsBit 1

PrimBinaryBool : Ty {C = 𝟚} ◇ 0ℓ
PrimBinaryBool = PrimFromPred ℕ IsBit

BinaryBool : NullaryTypeOp 𝟚 (λ _ → 0ℓ)
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


open import Data.Unit
open import Data.Empty.Polymorphic

always-false : Ctx ★ ℓ → Ctx 𝟚 ℓ
set (always-false Γ) type-obj = Γ ⟨ tt ⟩
set (always-false Γ) pred-obj = ⊥
rel (always-false Γ) type-id = id
rel (always-false Γ) pred-id = id
rel (always-false Γ) type-pred = ⊥-elim
rel-id (always-false Γ) {x = type-obj} _ = refl
rel-comp (always-false Γ) type-id g _ = refl
rel-comp (always-false Γ) pred-id g _ = refl
rel-comp (always-false Γ) type-pred pred-id _ = refl

always-false-subst : {Δ : Ctx ★ ℓ} {Γ : Ctx ★ ℓ'} → Δ ⇒ Γ → always-false Δ ⇒ always-false Γ
func (always-false-subst σ) {x = type-obj} = func σ
func (always-false-subst σ) {x = pred-obj} = ⊥-elim
_⇒_.naturality (always-false-subst σ) {f = type-id} _ = refl

always-false-subst-id : {Γ : Ctx ★ ℓ} → always-false-subst (id-subst Γ) ≅ˢ id-subst (always-false Γ)
eq always-false-subst-id {x = type-obj} _ = refl

always-false-subst-⊚ : {Δ : Ctx ★ ℓ} {Γ : Ctx ★ ℓ'} {Θ : Ctx ★ ℓ''} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                       always-false-subst (σ ⊚ τ) ≅ˢ always-false-subst σ ⊚ always-false-subst τ
eq (always-false-subst-⊚ σ τ) {x = type-obj} _ = refl

forget : {Γ : Ctx ★ ℓ} → Ty (always-false Γ) ℓ' → Ty Γ ℓ'
type (forget T) tt γ = T ⟨ type-obj , γ ⟩
morph (forget {Γ = Γ} T) tt eγ = T ⟪ type-id , trans (sym (rel-id Γ _ )) eγ ⟫
morph-cong (forget T) refl {eγ = refl} {eγ' = refl} = refl
morph-id (forget T) t = trans (morph-cong T refl) (morph-id T t)
morph-comp (forget T) _ _ _ _ t = sym (morph-cong-2-1 T refl)

module _ {Γ : Ctx ★ ℓ} {T : Ty (always-false Γ) ℓ'} where
  forget-intro : Tm (always-false Γ) T → Tm Γ (forget T)
  term (forget-intro t) tt γ = t ⟨ type-obj , γ ⟩'
  Tm.naturality (forget-intro t) tt _ = Tm.naturality t type-id _

  forget-elim : Tm Γ (forget T) → Tm (always-false Γ) T
  term (forget-elim t) type-obj γ = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-elim t) type-id eγ = trans (morph-cong T refl) (Tm.naturality t tt (trans (rel-id Γ _) eγ))

forget-natural : {Δ : Ctx ★ ℓ} {Γ : Ctx ★ ℓ'} (σ : Δ ⇒ Γ)
                 {T : Ty (always-false Γ) ℓ''} →
                 (forget T) [ σ ] ≅ᵗʸ forget (T [ always-false-subst σ ])
func (from (forget-natural σ)) = id
CwF-Structure.naturality (from (forget-natural σ {T = T})) _ = morph-cong T refl
func (to (forget-natural σ)) = id
CwF-Structure.naturality (to (forget-natural σ {T = T})) _ = morph-cong T refl
eq (isoˡ (forget-natural σ)) _ = refl
eq (isoʳ (forget-natural σ)) _ = refl

forget-cong : {Γ : Ctx ★ ℓ} {T : Ty (always-false Γ) ℓ'} {T' : Ty (always-false Γ) ℓ''} →
              T ≅ᵗʸ T' → forget T ≅ᵗʸ forget T'
func (from (forget-cong T=T')) = func (from T=T')
CwF-Structure.naturality (from (forget-cong T=T')) = CwF-Structure.naturality (from T=T')
func (to (forget-cong T=T')) = func (to T=T')
CwF-Structure.naturality (to (forget-cong T=T')) = CwF-Structure.naturality (to T=T')
eq (isoˡ (forget-cong T=T')) = eq (isoˡ T=T')
eq (isoʳ (forget-cong T=T')) = eq (isoʳ T=T')

instance
  always-false-functor : IsCtxFunctor always-false
  ctx-map {{always-false-functor}} = always-false-subst
  ctx-map-id {{always-false-functor}} = always-false-subst-id
  ctx-map-⊚ {{always-false-functor}} = always-false-subst-⊚

  forget-unarynat : IsUnaryNatural forget
  natural-un {{forget-unarynat}} = forget-natural
  cong-un {{forget-unarynat}} = forget-cong


infixl 12 _⊛_
_⊛_ : {Γ : Ctx ★ ℓ} {A B : Ty (always-false Γ) ℓ'} →
      Tm Γ (forget (A ⇛ B)) → Tm Γ (forget A) → Tm Γ (forget B)
f ⊛ a = forget-intro (forget-elim f $ forget-elim a)

binary-or : Tm Γ (BinaryBool ⇛ BinaryBool ⇛ BinaryBool)
binary-or = or BinaryBool

binary-or★ : {Γ : Ctx ★ 0ℓ} → Tm Γ (forget BinaryBool ⇛ forget BinaryBool ⇛ forget BinaryBool)
binary-or★ = lamι[ "x" ∈ forget BinaryBool ] lamι[ "y" ∈ forget BinaryBool ]
             forget-intro binary-or ⊛ varι "x" ⊛ varι "y"

open import Translation

instance
  forget-pred : {A : Set ℓ} {P : Pred A ℓ} → Translatable (forget (FromPred A P))
  Translatable.translated-type (forget-pred {A = A}) = A
  Translatable.translate-term forget-pred t = t ⟨ tt , tt ⟩'
  Translatable.translate-back forget-pred a = MkTm (λ _ _ → a) (λ _ _ → refl)
  Translatable.translate-cong forget-pred t=s = eq t=s tt
{-
binary-or-agda : ℕ → ℕ → ℕ
binary-or-agda = translate-term binary-or★

translate-result : (IsBit ⟨→⟩ IsBit ⟨→⟩ IsBit) binary-or-agda
translate-result {m} x {n} y = proj₂ ((binary-or {Γ = ◇} €⟨ pred-obj , tt ⟩ [ m , x ]) $⟨ pred-id , refl ⟩ [ n , y ])
-}
