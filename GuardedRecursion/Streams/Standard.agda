{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with coinductive streams of natural numbers in mode ★
--
-- Note that the option omega-in-omega is used to
-- make the type Stream' an instance of IsNullaryNatural.
-- This code should typecheck without this option in Agda
-- 2.6.2 once released.
--------------------------------------------------

module GuardedRecursion.Streams.Standard where

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
    fℓ gℓ : Level → Level
    Γ : Ctx ★ ℓ


discr-allnow : {Γ : Ctx ★ ℓc} {A : Set ℓ} →
               allnow-ty (Discr A) ≅ᵗʸ Discr {Γ = Γ} A
func (from discr-allnow) t = t ⟨ 0 , tt ⟩'
CwF-Structure.naturality (from discr-allnow) _ = refl
term (func (to discr-allnow) a) n _ = a
Tm.naturality (func (to discr-allnow) a) _ _ = refl
CwF-Structure.naturality (to discr-allnow) a = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoˡ discr-allnow) t = tm-≅-to-≡ (record { eq = λ _ → sym (Tm.naturality t z≤n refl) })
eq (isoʳ discr-allnow) _ = refl

{-
Stream' : {Γ : Ctx ★ ℓc} → Ty Γ ℓ → Ty Γ ℓ
Stream' A = allnow-ty (GStream (A [ from now-timeless-ctx ]))

instance
  stream'-un : IsUnaryNatural Stream'
  natural-un {{stream'-un}} σ {T = T} =
    ≅ᵗʸ-trans (allnow-ty-natural σ _) (allnow-ty-cong (
              ≅ᵗʸ-trans (gstream-natural (timeless-subst σ)) (gstream-cong (
                        ty-subst-seq-cong (from now-timeless-ctx ∷ (now-subst (timeless-subst σ) ◼))
                                          (σ ∷ (from now-timeless-ctx ◼))
                                          T
                                          (now-timeless-natural σ)))))
  cong-un {{stream'-un}} = allnow-ty-cong ∘ gstream-cong ∘ ty-subst-cong-ty _

module _ {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} where
  head' : Tm Γ (Stream' A ⇛ A)
  head' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ allnow-timeless-ty A ] allnow-tm (g-head $ unallnow-tm (varι "s"))

  tail' : Tm Γ (Stream' A ⇛ Stream' A)
  tail' = lamι[ "s" ∈ Stream' A ] ι[ allnow-later'-ty _ ] allnow-tm (g-tail $ unallnow-tm (varι "s"))

  cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
  cons' = lamι[ "x" ∈ A ]
            lamι[ "xs" ∈ Stream' A ]
              allnow-tm (g-cons $ unallnow-tm (ι[ allnow-timeless-ty A ] varι "x")
                                $ unallnow-tm (ι⁻¹[ allnow-later'-ty _ ] varι "xs"))

paperfolds' : Tm Γ (Stream' Nat')
paperfolds' = allnow-tm (ι[ by-naturality ] g-paperfolds)

fibs' : Tm Γ (Stream' Nat')
fibs' = allnow-tm (ι[ by-naturality ] g-fibs)

map' : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} {B : NullaryTypeOp ★ ℓ'} {{_ : IsNullaryNatural B}} →
       Tm Γ ((A ⇛ B) ⇛ Stream' A ⇛ Stream' B)
map' {A = A}{B = B} =
  lamι[ "f" ∈ A ⇛ B ]
    lamι[ "s" ∈ Stream' A ]
      allnow-tm (ι[ by-naturality ]
        (g-map $ timeless-tm (ι[ by-naturality ] (varι "f" [ from now-timeless-ctx ]'))
               $ unallnow-tm (ι[ allnow-ty-cong by-naturality ] varι "s")))

open import Reflection.Tactic.LobInduction

module _ {Γ : Ctx ω ℓc} {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} where
  g-every2nd : Tm Γ (timeless-ty (Stream' A) ⇛ GStream A)
  g-every2nd = löbι[ "g" ∈▻' (timeless-ty (Stream' A) ⇛ GStream A) ]
                 lamι[ "s" ∈ timeless-ty (Stream' A) ]
                   g-cons $ timeless-tm (head' $ untimeless-tm (varι "s"))
                          $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "s"))))

  instance
    stream-a-nat : IsNullaryNatural (Stream' A)
    natural-nul {{stream-a-nat}} σ = ≅ᵗʸ-trans (natural-un σ) (cong-un (natural-nul σ))

  g-diag : Tm Γ (timeless-ty (Stream' (Stream' A)) ⇛ GStream A)
  g-diag = löbι[ "g" ∈▻' (timeless-ty (Stream' (Stream' A)) ⇛ GStream A) ]
             lamι[ "xss" ∈ timeless-ty (Stream' (Stream' A)) ]
               g-cons $ timeless-tm (head' $ (head' $ untimeless-tm (varι "xss")))
                      $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "xss"))))

every2nd : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} →
           Tm Γ (Stream' A ⇛ Stream' A)
every2nd {A = A} =
  lamι[ "s" ∈ Stream' A ]
    allnow-tm (ι[ by-naturality ] (
      g-every2nd {A = A} $ timeless-tm (ι[ by-naturality ] (varι "s" [ from now-timeless-ctx ]'))))

diag : {A : NullaryTypeOp ★ ℓ} {{_ : IsNullaryNatural A}} →
       Tm Γ (Stream' (Stream' A) ⇛ Stream' A)
diag {A = A} =
  lamι[ "xss" ∈ Stream' (Stream' A) ]
    allnow-tm (ι[ by-naturality ] (
      g-diag {A = A} $ timeless-tm (ι[ by-naturality ] (varι "xss" [ from now-timeless-ctx ]'))))
-}

Stream' : NullaryTypeOp ★ fℓ → NullaryTypeOp ★ fℓ
Stream' A = allnow-ty (GStream A)

instance
  stream'-nul : {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} → IsNullaryNatural (Stream' A)
  natural-nul {{stream'-nul}} σ =
    ≅ᵗʸ-trans (allnow-ty-natural σ _) (allnow-ty-cong
              (≅ᵗʸ-trans (gstream-natural (timeless-subst σ)) (gstream-cong
                         (natural-nul (now-subst (timeless-subst σ))))))

module _ {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} where
  allnow-timeless-ty-nul : {Γ : Ctx ★ ℓc} → allnow-ty (timeless-ty A) ≅ᵗʸ A {Γ = Γ}
  allnow-timeless-ty-nul = ≅ᵗʸ-trans by-naturality (allnow-timeless-ty A)

  head' : Tm Γ (Stream' A ⇛ A)
  head' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ allnow-timeless-ty-nul ] allnow-tm (g-head $ unallnow-tm (varι "s"))

  tail' : Tm Γ (Stream' A ⇛ Stream' A)
  tail' = lamι[ "s" ∈ Stream' A ] ι[ allnow-later'-ty _ ] allnow-tm (g-tail $ unallnow-tm (varι "s"))

  cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
  cons' = lamι[ "x" ∈ A ]
            lamι[ "xs" ∈ Stream' A ]
              allnow-tm (g-cons $ unallnow-tm (ι[ allnow-timeless-ty-nul ] varι "x")
                                $ unallnow-tm (ι⁻¹[ allnow-later'-ty _ ] varι "xs"))

paperfolds' : Tm Γ (Stream' Nat')
paperfolds' = allnow-tm g-paperfolds

fibs' : Tm Γ (Stream' Nat')
fibs' = allnow-tm g-fibs

now-timeless-ctx-nul : {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} {Γ : Ctx ★ ℓc} →
                       Tm Γ A → Tm (now (timeless-ctx Γ)) A
now-timeless-ctx-nul t = ι[ by-naturality ] (t [ from now-timeless-ctx ]')

instance
  ⇛-nul : {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} {B : NullaryTypeOp ★ gℓ} {{_ : IsNullaryNatural B}} →
          IsNullaryNatural (A ⇛ B)
  natural-nul {{⇛-nul}} σ = by-naturality

map' : {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} {B : NullaryTypeOp ★ gℓ} {{_ : IsNullaryNatural B}} →
       Tm Γ ((A ⇛ B) ⇛ Stream' A ⇛ Stream' B)
map' {A = A}{B = B} =
  lamι[ "f" ∈ A ⇛ B ]
    lamι[ "s" ∈ Stream' A ]
      allnow-tm (g-map $ timeless-tm (now-timeless-ctx-nul (varι "f"))
                       $ unallnow-tm (varι "s"))

open import Reflection.Tactic.LobInduction

module _ {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} {Γ : Ctx ω ℓc} where
  g-every2nd : Tm Γ (timeless-ty (Stream' A) ⇛ GStream A)
  g-every2nd = löbι[ "g" ∈▻' (timeless-ty (Stream' A) ⇛ GStream A) ]
                 lamι[ "s" ∈ timeless-ty (Stream' A) ]
                   g-cons $ timeless-tm (head' $ untimeless-tm (varι "s"))
                          $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "s"))))

  g-diag : Tm Γ (timeless-ty (Stream' (Stream' A)) ⇛ GStream A)
  g-diag = löbι[ "g" ∈▻' (timeless-ty (Stream' (Stream' A)) ⇛ GStream A) ]
             lamι[ "xss" ∈ timeless-ty (Stream' (Stream' A)) ]
               g-cons $ timeless-tm (head' $ (head' $ untimeless-tm (varι "xss")))
                      $ varι "g" ⊛' next' (timeless-tm (tail' $ (tail' $ untimeless-tm (varι "xss"))))

every2nd : {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} →
           Tm Γ (Stream' A ⇛ Stream' A)
every2nd {A = A} = lamι[ "s" ∈ Stream' A ] allnow-tm (
                     g-every2nd $ timeless-tm (now-timeless-ctx-nul (varι "s")))

diag : {A : NullaryTypeOp ★ fℓ} {{_ : IsNullaryNatural A}} →
       Tm Γ (Stream' (Stream' A) ⇛ Stream' A)
diag {A = A} = lamι[ "xss" ∈ Stream' (Stream' A) ] allnow-tm (
                 g-diag $ timeless-tm (now-timeless-ctx-nul (varι "xss")))
