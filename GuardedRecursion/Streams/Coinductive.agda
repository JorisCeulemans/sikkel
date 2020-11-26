{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with coinductive streams of natural numbers in mode ★
--
-- Note that the option omega-in-omega is used to
-- make the type Stream' an instance of IsNullaryNatural.
-- This code should typecheck without this option in Agda
-- 2.6.2 once released.
--------------------------------------------------

module GuardedRecursion.Streams.Coinductive where

open import Data.Nat
open import Data.Unit
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import Types.Products
open import GuardedRecursion.Streams.Guarded
open import GuardedRecursion.Modalities
open import Reflection.Naturality
open import Reflection.Tactic.Lambda
open import Reflection.Naturality.Instances

private
  variable
    ℓ ℓc : Level
    Γ : Ctx ★ ℓ


discr-global : {Γ : Ctx ★ ℓc} {A : Set ℓ} →
               global-ty (Discr A) ≅ᵗʸ Discr {Γ = Γ} A
func (from discr-global) t = t ⟨ 0 , tt ⟩'
CwF-Structure.naturality (from discr-global) _ = refl
term (func (to discr-global) a) n _ = a
Tm.naturality (func (to discr-global) a) _ _ = refl
CwF-Structure.naturality (to discr-global) a = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoˡ discr-global) t = tm-≅-to-≡ (record { eq = λ _ → sym (Tm.naturality t z≤n refl) })
eq (isoʳ discr-global) _ = refl

Stream' : {Γ : Ctx ★ ℓ} → Ty Γ 0ℓ
Stream' = global-ty GStream

instance
  stream'-nul : IsNullaryNatural Stream'
  IsNullaryNatural.natural-nul stream'-nul σ = ≅ᵗʸ-trans (global-ty-natural σ GStream)
                                                         (global-ty-cong (gstream-natural (timeless-subst σ)))

head' : Tm Γ (Stream' ⇛ Nat')
head' = lamι Stream' (ι⁻¹[ discr-global ] global-tm (g-head $ unglobal-tm (varι 0)))

tail' : Tm Γ (Stream' ⇛ Stream')
tail' = lamι Stream' (ι[ global-later'-ty GStream ] global-tm (g-tail $ unglobal-tm (varι 0)))

cons' : Tm Γ (Nat' ⇛ Stream' ⇛ Stream')
cons' = lamι Nat' (
             lamι Stream' (
                  global-tm (g-cons $ pair (unglobal-tm (ι[ discr-global ] varι 1))
                                           (unglobal-tm (ι⁻¹[ global-later'-ty GStream ] varι 0)))))

paperfolds' : Tm Γ Stream'
paperfolds' = global-tm g-paperfolds

fibs' : Tm Γ Stream'
fibs' = global-tm g-fibs
