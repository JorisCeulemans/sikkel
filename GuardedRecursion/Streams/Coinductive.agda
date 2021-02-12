{-# OPTIONS --omega-in-omega --allow-unsolved-metas #-}

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
open import Function using (id; _∘_)
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
open import Reflection.Tactic.Naturality
open import Reflection.Naturality.Instances
open import Reflection.SubstitutionSequence

private
  variable
    ℓ ℓ' ℓc : Level
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

Stream' : {Γ : Ctx ★ ℓc} → Ty Γ ℓ → Ty Γ ℓ
Stream' A = global-ty (GStream (A [ from now-timeless-ctx ]))

instance
  stream'-un : IsUnaryNatural Stream'
  natural-un {{stream'-un}} σ {T = T} =
    ≅ᵗʸ-trans (global-ty-natural σ _) (global-ty-cong (
              ≅ᵗʸ-trans (gstream-natural (timeless-subst σ)) (gstream-cong (
                        ty-subst-seq-cong (from now-timeless-ctx ∷ (now-subst (timeless-subst σ) ◼))
                                          (σ ∷ (from now-timeless-ctx ◼))
                                          T
                                          (now-timeless-natural σ)))))
  cong-un {{stream'-un}} = global-ty-cong ∘ gstream-cong ∘ ty-subst-cong-ty _

module _ {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} where
  head' : Tm Γ (Stream' A ⇛ A)
  head' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ global-timeless-ty A ] global-tm (g-head $ unglobal-tm (varι "s"))

  tail' : Tm Γ (Stream' A ⇛ Stream' A)
  tail' = lamι[ "s" ∈ Stream' A ] ι[ global-later'-ty _ ] global-tm (g-tail $ unglobal-tm (varι "s"))

  cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
  cons' = lamι[ "x" ∈ A ]
            lamι[ "xs" ∈ Stream' A ]
              global-tm (g-cons $ unglobal-tm (ι[ global-timeless-ty A ] varι "x")
                                $ unglobal-tm (ι⁻¹[ global-later'-ty _ ] varι "xs"))

paperfolds' : Tm Γ (Stream' Nat')
paperfolds' = global-tm (ι[ by-naturality ] g-paperfolds)

fibs' : Tm Γ (Stream' Nat')
fibs' = global-tm (ι[ by-naturality ] g-fibs)

map' : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} {B : NullaryTypeOp ★ ℓ'} {{_ : IsNullaryNatural B}} →
       Tm Γ ((A ⇛ B) ⇛ Stream' A ⇛ Stream' B)
map' {A = A}{B = B} = lamι[ "f" ∈ A ⇛ B ] lamι[ "s" ∈ Stream' A ] global-tm {!!}

open import Reflection.Tactic.LobInduction

module _ {Γ : Ctx ω ℓc} {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} where
  every2nd : Tm Γ (timeless-ty (Stream' A) ⇛ GStream A)
  every2nd = löbι[ "g" ∈ timeless-ty (Stream' A) ⇛ GStream A ]
               lamι[ "s" ∈ timeless-ty (Stream' A) ]
                 g-cons $ timeless-tm (head' $ untimeless-tm (varι "s"))
                        $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "s"))))

  instance
    stream-a-nat : IsNullaryNatural (Stream' A)
    natural-nul {{stream-a-nat}} σ = ≅ᵗʸ-trans (natural-un σ) (cong-un (natural-nul σ))

  g-diag : Tm Γ (timeless-ty (Stream' (Stream' A)) ⇛ GStream A)
  g-diag = löbι[ "g" ∈ timeless-ty (Stream' (Stream' A)) ⇛ GStream A ]
             lamι[ "xss" ∈ timeless-ty (Stream' (Stream' A)) ]
               g-cons $ timeless-tm (head' $ (head' $ untimeless-tm (varι "xss")))
                      $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "xss"))))

diag : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} →
       Tm Γ (Stream' (Stream' A) ⇛ Stream' A)
diag {A = A} = lamι[ "xss" ∈ Stream' (Stream' A) ] global-tm {!g-diag $ ?!}
