-- {-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Substitution Sequences
--
-- This module contains some results on applying a sequence of
-- substitutions to a type or a term. The main results are
-- ty-subst-seq-cong and tm-subst-seq-cong (although the latter
-- isn't really used anywhere).
-- Note that we use the option omega-in-omega in order to define
-- an inductive data type in Setω and to pattern match on it (which
-- is not possible in Agda 2.6.1 without this option). This code should
-- typecheck without this option in Agda 2.6.2 once released (tested with
-- the development version on July 10, 2020).
--------------------------------------------------

open import Categories

module Reflection.SubstitutionSequence {C : Category} where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

infixr 5 _∷_

private
  variable
    Δ Γ : Ctx C
    T : Ty Γ


-- Type of a sequence of substitutions. The order is as if you would compose them.
data _⇒⁺_ : Ctx C → Ctx C → Set₁ where
  _◼ : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) → Δ ⇒⁺ Γ
  _∷_ : ∀ {Δ : Ctx C} {Γ : Ctx C} {Θ : Ctx C} (σ : Γ ⇒ Θ) (σs : Δ ⇒⁺ Γ) → Δ ⇒⁺ Θ

fold : Δ ⇒⁺ Γ → Δ ⇒ Γ
fold (σ ◼) = σ
fold (σ ∷ σs) = σ ⊚ fold σs

-- Applying a sequence of substitutions to a type.
_⟦_⟧ : (T : Ty Γ) (σs : Δ ⇒⁺ Γ) → Ty Δ
T ⟦ σ ◼ ⟧ = T [ σ ]
T ⟦ σ ∷ σs ⟧ = (T [ σ ]) ⟦ σs ⟧

-- Applying a sequence of substitutions to a term.
_⟦_⟧' : (t : Tm Γ T) (σs : Δ ⇒⁺ Γ) → Tm Δ (T ⟦ σs ⟧)
t ⟦ σ ◼ ⟧' = t [ σ ]'
t ⟦ σ ∷ σs ⟧' = (t [ σ ]') ⟦ σs ⟧'

ty-subst-seq-fold : (σs : Δ ⇒⁺ Γ) (T : Ty Γ) →
                    T ⟦ σs ⟧ ≅ᵗʸ T [ fold σs ]
ty-subst-seq-fold (σ ◼) T = ≅ᵗʸ-refl
ty-subst-seq-fold (σ ∷ σs) T = ≅ᵗʸ-trans (ty-subst-seq-fold σs (T [ σ ]))
                                         (ty-subst-comp T σ (fold σs))

tm-subst-seq-fold : (σs : Δ ⇒⁺ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    t ⟦ σs ⟧' ≅ᵗᵐ ι[ ty-subst-seq-fold σs T ] (t [ fold σs ]')
tm-subst-seq-fold (σ ◼) t = ≅ᵗᵐ-sym (ι-refl _)
tm-subst-seq-fold {Δ = Δ}{Γ} (σ ∷ σs) {T} t =
  begin
    (t [ σ ]') ⟦ σs ⟧'
  ≅⟨ tm-subst-seq-fold σs (t [ σ ]') ⟩
    ι[ ty-subst-seq-fold σs (T [ σ ]) ] ((t [ σ ]') [ fold σs ]')
  ≅⟨ ι-cong (ty-subst-seq-fold σs (T [ σ ])) (tm-subst-comp t σ (fold σs)) ⟩
    ι[ ty-subst-seq-fold σs (T [ σ ]) ] (ι[ ty-subst-comp T σ (fold σs) ] (t [ σ ⊚ fold σs ]'))
  ≅˘⟨ ι-trans (ty-subst-seq-fold σs (T [ σ ])) (ty-subst-comp T σ (fold σs)) (t [ σ ⊚ fold σs ]') ⟩
    ι[ ≅ᵗʸ-trans (ty-subst-seq-fold σs (T [ σ ])) (ty-subst-comp T σ (fold σs)) ] (t [ σ ⊚ fold σs ]') ∎
  where open ≅ᵗᵐ-Reasoning

ty-subst-seq-cong : (σs τs : Δ ⇒⁺ Γ) (T : Ty Γ) →
                    fold σs ≅ˢ fold τs →
                    T ⟦ σs ⟧ ≅ᵗʸ T ⟦ τs ⟧
ty-subst-seq-cong σs τs T e =
  begin
    T ⟦ σs ⟧
  ≅⟨ ty-subst-seq-fold σs T ⟩
    T [ fold σs ]
  ≅⟨ ty-subst-cong-subst e T ⟩
    T [ fold τs ]
  ≅˘⟨ ty-subst-seq-fold τs T ⟩
    T ⟦ τs ⟧ ∎
  where open ≅ᵗʸ-Reasoning

tm-subst-seq-cong : (σs τs : Δ ⇒⁺ Γ) (t : Tm Γ T) →
                    (e : fold σs ≅ˢ fold τs) →
                    t ⟦ σs ⟧' ≅ᵗᵐ ι[ ty-subst-seq-cong σs τs T e ] (t ⟦ τs ⟧')
tm-subst-seq-cong {Δ = Δ} {T = T} σs τs t e =
  begin
    t ⟦ σs ⟧'
  ≅⟨ tm-subst-seq-fold σs t ⟩
    ι[ ty-subst-seq-fold σs T ] (t [ fold σs ]')
  ≅⟨ ι-cong (ty-subst-seq-fold σs T) (tm-subst-cong-subst t e) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (t [ fold τs ]'))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-symˡ (ty-subst-seq-fold τs T) (t [ fold τs ]'))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-sym (ty-subst-seq-fold τs T) ] (ι[ ty-subst-seq-fold τs T ] (t [ fold τs ]'))))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-cong (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) (tm-subst-seq-fold τs t))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-sym (ty-subst-seq-fold τs T) ] (t ⟦ τs ⟧')))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-cong (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) (ι-refl _))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-sym (ty-subst-seq-fold τs T) ] (ι[ ≅ᵗʸ-refl ] (t ⟦ τs ⟧'))))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl (t ⟦ τs ⟧'))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl ] (t ⟦ τs ⟧')))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl) (t ⟦ τs ⟧')) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ≅ᵗʸ-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl) ] (t ⟦ τs ⟧'))
  ≅˘⟨ ι-trans (ty-subst-seq-fold σs T) (≅ᵗʸ-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl)) (t ⟦ τs ⟧') ⟩
    ι[ ≅ᵗʸ-trans (ty-subst-seq-fold σs T) (≅ᵗʸ-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl)) ] (t ⟦ τs ⟧')
  ≅⟨⟩
    ι[ ty-subst-seq-cong σs τs T e ] (t ⟦ τs ⟧') ∎
  where open ≅ᵗᵐ-Reasoning
