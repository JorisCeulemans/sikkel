open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Archive.InductiveDerivations.TestIntrinsic
  (ℬ : BiSikkelParameter)
  where

open import Data.String

open BiSikkelParameter ℬ

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp.Named 𝒫 𝒷
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String
  Ξ : ProofCtx m


infix 1 _⊢_
data _⊢_ : (Ξ : ProofCtx m) → bProp (to-ctx Ξ) → Set where
  -- Making sure that derivability respects alpha equivalence. This is
  --  not ideal, we would like to bake this into assumption' below.
  --  However see comment on withTmAlpha below for problems with that.
  -- withAlpha : {{ φ ≈αᶠ ψ }} → (Ξ ⊢ φ) → (Ξ ⊢ ψ)

  -- Functoriality of the locks in a proof context
  -- lock𝟙-der : (Ξ ⊢ φ) → (Ξ ,lock⟨ 𝟙 ⟩ ⊢ lock𝟙-frm φ)
  -- unlock𝟙-der : (Ξ ,lock⟨ 𝟙 ⟩ ⊢ φ) → (Ξ ⊢ unlock𝟙-frm φ)
  -- fuselocks-der : (Ξ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩ ⊢ φ) → (Ξ ,lock⟨ μ ⓜ ρ ⟩ ⊢ fuselocks-frm φ)
  -- unfuselocks-der : (Ξ ,lock⟨ μ ⓜ ρ ⟩ ⊢ φ) → (Ξ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩ ⊢ unfuselocks-frm φ)

  -- Structural rules for ≡ᵇ
  refl : {t : Tm (to-ctx Ξ) T} → Ξ ⊢ t ≡ᵇ t
  sym : {t1 t2 : Tm (to-ctx Ξ) T} → (Ξ ⊢ t1 ≡ᵇ t2) → (Ξ ⊢ t2 ≡ᵇ t1)
  trans : {t1 t2 t3 : Tm (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᵇ t2) → (Ξ ⊢ t2 ≡ᵇ t3) →
          (Ξ ⊢ t1 ≡ᵇ t3)
  subst : (φ : bProp (to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T))) {t1 t2 : Tm (to-ctx (Ξ ,lock⟨ μ ⟩)) T} →
          (Ξ ,lock⟨ μ ⟩ ⊢ t1 ≡ᵇ t2) →
          (Ξ ⊢ φ [ t1 / x ]bpropˢ) →
          (Ξ ⊢ φ [ t2 / x ]bpropˢ)

  -- Introduction and elimination for logical combinators ⊤ᵇ, ⊥ᵇ, ⊃, ∧ and ∀
  ⊤ᵇ-intro : Ξ ⊢ ⊤ᵇ
  ⊥ᵇ-elim : Ξ ⊢ ⊥ᵇ → Ξ ⊢ φ
  assume[_∣_]_ : (μ : Modality m n) {φ : bProp ((to-ctx Ξ) ,lock⟨ μ ⟩)} (x : String) →
                 (Ξ ,,ᵇ μ ∣ x ∈ φ ⊢ ψ) →
                 (Ξ ⊢ ⟨ μ ∣ φ ⟩ ⊃ ψ)
  ⊃-elim : (Ξ ⊢ ⟨ μ ∣ φ ⟩ ⊃ ψ) → (Ξ ,lock⟨ μ ⟩ ⊢ φ) → (Ξ ⊢ ψ)
  assumption : {x : String} (a : Assumption x Ξ ◇) (α : TwoCell (as-mod a) (locksˡᵗ (as-lt a)))→ (Ξ ⊢ lookup-assumption a α)
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  ∀-intro : (Ξ ,,ᵛ μ ∣ x ∈ T ⊢ φ) → (Ξ ⊢ ∀[ μ ∣ x ∈ T ] φ)
  ∀-elim : (Ξ ⊢ ∀[ μ ∣ x ∈ T ] φ) → (t : Tm ((to-ctx Ξ) ,lock⟨ μ ⟩) T) → (Ξ ⊢ φ [ t / x ]bpropˢ)

  -- Modal reasoning principles
  mod⟨_⟩_ : (μ : Modality m n) {φ : bProp (to-ctx (Ξ ,lock⟨ μ ⟩))} →
            (Ξ ,lock⟨ μ ⟩ ⊢ φ) →
            (Ξ ⊢ ⟨ μ ∣ φ ⟩)
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : String) {φ : bProp _} →
             (Ξ ,lock⟨ ρ ⟩ ⊢ ⟨ μ ∣ φ ⟩) →
             (Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ ⊢ ψ) →
             (Ξ ⊢ ψ)

  -- Specific computation rules for term formers (currently no eta rules)
  fun-β : {b : Tm (to-ctx Ξ ,, μ ∣ x ∈ T) S} {t : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T} →
          (Ξ ⊢ (lam[ μ ∣ x ∈ T ] b) ∙ t ≡ᵇ b [ t / x ]tmˢ)
  nat-rec-β-zero : {A : Ty m} {z : Tm (to-ctx Ξ) A} {s : Tm (to-ctx Ξ) (A ⇛ A)} →
                   (Ξ ⊢ nat-rec z s zero ≡ᵇ z)
  nat-rec-β-suc : {A : Ty m} {z : Tm (to-ctx Ξ) A} {s : Tm (to-ctx Ξ) (A ⇛ A)} {n : Tm (to-ctx Ξ) Nat'} →
                  (Ξ ⊢ nat-rec z s (suc n) ≡ᵇ s ∙¹ (nat-rec z s n))
  if-β-true : {t f : Tm (to-ctx Ξ) T} →
              (Ξ ⊢ if true t f ≡ᵇ t)
  if-β-false : {t f : Tm (to-ctx Ξ) T} →
               (Ξ ⊢ if false t f ≡ᵇ f)
  pair-β-fst : {t : Tm (to-ctx Ξ) T} {s : Tm (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᵇ t)
  pair-β-snd : {t : Tm (to-ctx Ξ) T} {s : Tm (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᵇ s)

  -- Axioms specifying distinctness of booleans and natural numbers
  true≠false : Ξ ⊢ ¬ (true ≡ᵇ false)
  suc-inj : {Ξ : ProofCtx m} → Ξ ⊢ ∀[ 𝟙 ∣ "m" ∈ Nat' ] ∀[ 𝟙 ∣ "n" ∈ Nat' ] (suc (svar "m") ≡ᵇ suc (svar "n")) ⊃ (svar "m" ≡ᵇ svar "n")
  zero≠sucn : Ξ ⊢ ∀[ 𝟙 ∣ "n" ∈ Nat' ] ¬ (zero ≡ᵇ suc (svar "n"))

  -- Induction schemata for Bool' and Nat'
  bool-induction : (Ξ ⊢ φ [ true  / x ]bpropˢ) →
                   (Ξ ⊢ φ [ false / x ]bpropˢ) →
                   (Ξ ,,ᵛ 𝟙 ∣ x ∈ Bool' ⊢ φ)
  nat-induction : (hyp : String) →
                  (Ξ ⊢ φ [ zero / x ]bpropˢ) →
                  (Ξ ,,ᵛ 𝟙 ∣ x ∈ Nat' ,,ᵇ 𝟙 ∣ hyp ∈ lock𝟙-bprop φ ⊢ φ [ suc v0 // x ]bpropˢ) →
                  (Ξ ,,ᵛ 𝟙 ∣ x ∈ Nat' ⊢ φ)
  mod-induction : (ρ : Modality o m) (μ : Modality n o) (y : String) {φ : bProp (to-ctx Ξ ,, ρ ∣ x ∈ ⟨ μ ∣ T ⟩)} →
                  (Ξ ,,ᵛ ρ ⓜ μ ∣ y ∈ T ⊢ φ [ (mod⟨ μ ⟩ var' y {vlock (vlock (vzero id-cell))}) // x ]bpropˢ) →
                  (Ξ ,,ᵛ ρ ∣ x ∈ ⟨ μ ∣ T ⟩ ⊢ φ)

  fun-cong : {f g : Tm (to-ctx Ξ) (⟨ μ ∣ T ⟩⇛ S)} {t : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T} →
             Ξ ⊢ f ≡ᵇ g →
             Ξ ⊢ f ∙ t ≡ᵇ g ∙ t
  cong : {f : Tm (to-ctx Ξ) (⟨ μ ∣ T ⟩⇛ S)} {t t' : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T} →
         Ξ ,lock⟨ μ ⟩ ⊢ t ≡ᵇ t' →
         Ξ ⊢ f ∙ t ≡ᵇ f ∙ t'
