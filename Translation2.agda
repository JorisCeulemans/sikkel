--------------------------------------------------
-- Extracting embedded terms in mode ★ to Agda
--------------------------------------------------

module Translation2 where

open import Function using (_∘_)
open import Data.Nat
open import Data.Product using (_×_;proj₁;proj₂) renaming (_,_ to [_,_])
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

open import Helpers
open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums
open import Types.Instances
open import Reflection.Tactic.Lambda
open import Modalities


--------------------------------------------------
-- Definition of the Translatable type class

record Translatable {C : Category} (T : Ty {C = C} ◇) : Set₁ where
  field
    translated-type : {x : Category.Ob C} → (xF : Final C x) → Set
    translate-term  : {x : Category.Ob C} → (xF : Final C x) → T ⟨ x , tt ⟩ → translated-type xF
    translate-back  : {x : Category.Ob C} → (xF : Final C x) → translated-type xF → T ⟨ x , tt ⟩

open Translatable {{...}} public

translate-type : ∀ {C} (T : Ty {C = C} ◇) → {{Translatable T}} → {x : Category.Ob C} → (xF : Final C x) → Set
translate-type T = translated-type {T = T}


--------------------------------------------------
-- Instances of Translatable for Sikkel's built-in types & type
-- constructors (discrete types, products, sums, functions)

instance
  translate-discr : ∀ {C} {A : Set} → Translatable {C = C} (Discr A)
  translated-type {{translate-discr {A = A}}} xF = A
  translate-term  {{translate-discr {A = A}}} xF t = t
  translate-back  {{translate-discr {A = A}}} xF a = a

  translate-prod : ∀ {C} {T : Ty {C = C} ◇} {{_ : Translatable T}}
                   {S : Ty ◇} {{_ : Translatable S}} →
                   Translatable (T ⊠ S)
  translated-type {{translate-prod {T = T} {S = S}}} xF = translate-type T xF × translate-type S xF
  translate-term  {{translate-prod {T = T} {S = S}}} xF p = [ translate-term xF (proj₁ p) , translate-term xF (proj₂ p) ]
  translate-back  {{translate-prod {T = T} {S = S}}} xF [ t , s ] = [ translate-back xF t , translate-back xF s ]

-- expose-sum-term : ∀ {C} {A : Ty {C = C} ◇} {B : Ty ◇} →
--                   Category.Ob C → Tm ◇ (A ⊞ B) → Tm ◇ A ⊎ Tm ◇ B
-- expose-sum-term {A = A}{B = B} x p with p ⟨ x , tt ⟩'
-- ... | inj₁ a = inj₁ (MkTm (λ { x tt → {!a!} }) {!λ { tt refl → ty-id A }!})
-- ... | inj₂ b = inj₂ {!MkTm (λ { x tt → ? }) (λ { tt refl → ty-id B })!}

instance
  translate-sum : ∀ {C} {T : Ty {C = C} ◇} {{_ : Translatable T}}
                  {S : Ty ◇} {{_ : Translatable S}} →
                  Translatable (T ⊞ S)
  translated-type {{translate-sum {T = T} {S = S}}} xF = translate-type T xF ⊎ translate-type S xF
  translate-term ⦃ translate-sum ⦄ x (inj₁ t) = inj₁ (translate-term x t)
  translate-term ⦃ translate-sum {T = T} {S = S} ⦄ xF (inj₂ s) = inj₂ (translate-term xF s)
  translate-back  {{translate-sum {T = T} {S = S}}} xF (inj₁ t) = inj₁ (translate-back xF t)
  translate-back  {{translate-sum {T = T} {S = S}}} xF (inj₂ s) = inj₂ (translate-back xF s)

-- A term in the empty context in mode ★ is nothing more than an Agda value.
to-★-◇-term : {T : Ty {C = ★} ◇} → T ⟨ tt , tt ⟩ → Tm ◇ T
to-★-◇-term t ⟨ _ , _ ⟩' = t
Tm.naturality (to-★-◇-term {T = T} t) _ refl = ty-id T

-- A function in the empty context in mode ★ is nothing more than an Agda function.
func-★-◇ : {T : Ty {C = ★} ◇} {S : Ty {C = ★} ◇} →
           (Tm ◇ T → Tm ◇ S) → Tm ◇ (T ⇛ S)
(func-★-◇ {T = T} f ⟨ _ , _ ⟩') $⟨ _ , refl ⟩ t = f (to-★-◇-term t) ⟨ tt , tt ⟩'
PresheafFunc.naturality (func-★-◇ {T = T}{S = S} f ⟨ _ , _ ⟩') {ρ-xy = _} {eγ-zy = refl} {refl} {t} =
  trans (cong (λ x → f (to-★-◇-term x) ⟨ tt , tt ⟩') (ty-id T)) (sym (ty-id S))
Tm.naturality (func-★-◇ f) _ refl = to-pshfun-eq (λ { _ refl _ → refl })

instance
  translate-func : ∀ {C} {T : Ty {C = C} ◇} {{_ : Translatable T}}
                   {S : Ty ◇} {{_ : Translatable S}} →
                   Translatable (T ⇛ S)
  translated-type {{translate-func {T = T} {S = S}}} xF = translate-type T xF → translate-type S xF
  translate-term  {{translate-func {C = C} {T = T} {S = S}}} xF f t = translate-term xF (f $⟨ Category.hom-id C , refl ⟩ translate-back xF t)
  _$⟨_,_⟩_ (translate-back ⦃ translate-func {T = T} {S = S} ⦄ {x = x} xF f) ρ refl t with xF [ _ , ρ ]
  _$⟨_,_⟩_ (translate-back ⦃ translate-func {T = T} {S = S} ⦄ {x = x} xF f) ρ refl t | refl =
    translate-back xF (f (translate-term xF t))
  PresheafFunc.naturality (translate-back ⦃ translate-func {T = T} {S = S} ⦄ {x = x} xF f) {x₁} {y} {ρ-xy} {ρ-yz} {._} {._} {refl} {refl} {t} with xF [ _ , ρ-yz ]
  PresheafFunc.naturality (translate-back ⦃ translate-func {C = C} {T = T} {{TransT}} {S = S} {{TransS}} ⦄ {x = x} xF f) {x₁} {y} {ρ-xy} {ρ-yz} {._} {._} {refl} {refl} {t} | refl = help
    where help2 : translate-back {{translate-func}} xF f $⟨ ρ-xy , refl ⟩ (T ⟪ ρ-xy , refl ⟫ t) ≡
               S ⟪ ρ-xy , refl ⟫ Translatable.translate-back TransS xF (f (Translatable.translate-term TransT xF t))
          help2 with xF [ x₁ , ρ-xy ]
          help2 | refl = trans (cong
                                  (λ x →
                                     Translatable.translate-back TransS xF
                                     (f (Translatable.translate-term TransT xF x)))
                                  (ty-id T)) (sym (ty-id S))
          help : translate-back {{translate-func}} xF f $⟨ Category._∙_ C (Category.hom-id C) ρ-xy , refl ⟩ (T ⟪ ρ-xy , refl ⟫ t) ≡
               S ⟪ ρ-xy , refl ⟫ Translatable.translate-back TransS xF (f (Translatable.translate-term TransT xF t))
          help = trans (cong (λ ρ-xy′ → translate-back {{translate-func {{TransT}} {{TransS}} }} xF f $⟨ ρ-xy′ , refl ⟩ (T ⟪ ρ-xy , refl ⟫ t)) (Category.hom-idˡ C)) help2


--------------------------------------------------
-- Example: translating addition of natural numbers from Sikkel to Agda

translate-term′ : ∀ {C} {T : Ty {C = C} ◇} {{transT : Translatable T}} →
                (x : Category.Ob C) (xF : Final C x) → Tm {C = C} ◇ T → Translatable.translated-type transT xF
translate-term′ {C} {T} {{transT}} x xF t = translate-term {C = C} {T = T} {x = x} xF (Tm.term t x tt)

private
  -- Definition of addition in Sikkel using the recursion principle for Nat'.
  nat-sum' : Tm {C = ★} ◇ (Nat' ⇛ Nat' ⇛ Nat')
  nat-sum' = nat-elim (Nat' ⇛ Nat')
                      (lamι[ "n" ∈ Nat' ] varι "n")
                      (lamι[ "f" ∈ Nat' ⇛ Nat' ] lamι[ "n" ∈ Nat' ] suc' $ (varι "f" $ varι "n"))

  _+'_ : ℕ → ℕ → ℕ
  _+'_ = translate-term′ tt (λ _ → refl) nat-sum'

  test : 6 +' 3 ≡ 9
  test = refl
