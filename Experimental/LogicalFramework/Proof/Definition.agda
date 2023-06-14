--------------------------------------------------
-- Definition of proofs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.Proof.Definition (ℳ : ModeTheory) where

open import Data.String as Str hiding (_≟_)
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Syntax ℳ
open import Experimental.LogicalFramework.bProp.Named ℳ

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String


data Proof {m : Mode} : Ctx m → Set where
  {-
  -- Functoriality of the locks in a proof context
  lock𝟙-der : (Ξ ⊢ φ) → (Ξ ,lock⟨ 𝟙 ⟩ ⊢ lock𝟙-bprop φ)
  unlock𝟙-der : (Ξ ,lock⟨ 𝟙 ⟩ ⊢ φ) → (Ξ ⊢ unlock𝟙-bprop φ)
  fuselocks-der : (Ξ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩ ⊢ φ) → (Ξ ,lock⟨ μ ⓜ ρ ⟩ ⊢ fuselocks-bprop φ)
  unfuselocks-der : (Ξ ,lock⟨ μ ⓜ ρ ⟩ ⊢ φ) → (Ξ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩ ⊢ unfuselocks-bprop φ)
  -}

  -- Structural rules for ≡ᵇ
  refl : Proof Γ  -- Ξ ⊢ t ≡ᵇ t
  sym : Proof Γ  -- Ξ ⊢ t ≡ᵇ s
        →
        Proof Γ  -- Ξ ⊢ s ≡ᵇ t
  trans : (t : Tm Γ T) →
          Proof Γ →  -- Ξ ⊢ r ≡ᵇ t
          Proof Γ     -- Ξ ⊢ t ≡ᵇ s
          →
          Proof Γ     -- Ξ ⊢ r ≡ᵇ s
  subst : (φ : bProp (Γ ,, μ ∣ x ∈ T)) (t1 t2 : Tm (Γ ,lock⟨ μ ⟩) T) →
          Proof (Γ ,lock⟨ μ ⟩) →  -- Ξ ,lock⟨ μ ⟩ ⊢ t1 ≡ᵇ t2
          Proof Γ                 -- Ξ ⊢ φ [ t1 / x ]bprop
          →
          Proof Γ                 -- Ξ ⊢ φ [ t2 / x ]bprop

  {-
  -- Introduction and elimination for logical combinators ⊤ᵇ, ⊥ᵇ, ⊃, ∧ and ∀
  ⊤ᵇ-intro : Ξ ⊢ ⊤ᵇ
  ⊥ᵇ-elim : Ξ ⊢ ⊥ᵇ ⊃ φ
  assume[_∣_]_ : (μ : Modality m n) {φ : bProp ((to-ctx Ξ) ,lock⟨ μ ⟩)} (x : String) →
                 (Ξ ,,ᵇ μ ∣ x ∈ φ ⊢ ψ) →
                 (Ξ ⊢ ⟨ μ ∣ φ ⟩ ⊃ ψ)
  ⊃-elim : (Ξ ⊢ ⟨ μ ∣ φ ⟩ ⊃ ψ) → (Ξ ,lock⟨ μ ⟩ ⊢ φ) → (Ξ ⊢ ψ)
  -}
  assumption' : (x : String) {μ κ : Modality m n} (α : TwoCell μ κ) → Proof Γ
  {-
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  -}
  ∀-intro[_∣_∈_]_ : (μ : Modality n m) (x : String) (T : Ty n) → Proof (Γ ,, μ ∣ x ∈ T) → Proof Γ
  ∀-elim : (μ : Modality n m) (φ : bProp Γ) → Proof Γ → (t : Tm (Γ ,lock⟨ μ ⟩) T) → Proof Γ
  {-

  -- Modal reasoning principles
  mod⟨_⟩_ : (μ : Modality m n) {φ : bProp (to-ctx (Ξ ,lock⟨ μ ⟩))} →
            (Ξ ,lock⟨ μ ⟩ ⊢ φ) →
            (Ξ ⊢ ⟨ μ ∣ φ ⟩)
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : String) {φ : bProp _} →
             (Ξ ,lock⟨ ρ ⟩ ⊢ ⟨ μ ∣ φ ⟩) →
             (Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ ⊢ ψ) →
             (Ξ ⊢ ψ)
  -}

  -- Specific computation rules for term formers (currently no eta rules)
  fun-β : Proof Γ
  nat-rec-β-zero : Proof Γ
  nat-rec-β-suc : Proof Γ
  {-
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
  suc-inj : {Ξ : ProofCtx m} → Ξ ⊢ ∀[ 𝟙 ∣ "m" ∈ Nat' ] ∀[ 𝟙 ∣ "n" ∈ Nat' ] (suc ∙ (svar "m") ≡ᵇ suc ∙ (svar "n")) ⊃ (svar "m" ≡ᵇ svar "n")
  zero≠sucn : Ξ ⊢ ∀[ 𝟙 ∣ "n" ∈ Nat' ] ¬ (zero ≡ᵇ suc ∙ svar "n")

  -- Induction schemata for Bool' and Nat'
  bool-induction : (Ξ ⊢ φ [ true / x ]bprop) →
                   (Ξ ⊢ φ [ false / x ]bprop) →
                   (Ξ ,,ᵛ μ ∣ x ∈ Bool' ⊢ φ)
  -}
  nat-induction' : {Γ Δ : Ctx m} {x : String} (hyp : String) → Δ Ag.≡ (Γ ,, x ∈ Nat') →
                   Proof Γ → Proof Δ → Proof Δ
    -- ^ We cannot just return a proof of type Proof (Γ ,, x ∈ Nat')
    -- because in that case pattern matching in the proof checker
    -- would fail. Users are intended to use nat-induction defined below.

  fun-cong : Proof Γ → Tm (Γ ,lock⟨ μ ⟩) T → Proof Γ
  cong : {T S : Ty m} → Tm Γ (⟨ μ ∣ T ⟩⇛ S) → Proof (Γ ,lock⟨ μ ⟩) → Proof Γ
  hole : String → Proof Γ

nat-induction : {Γ : Ctx m} {x : String} (hyp : String) →
                Proof Γ → Proof (Γ ,, x ∈ Nat') → Proof (Γ ,, x ∈ Nat')
nat-induction hyp = nat-induction' hyp Ag.refl
