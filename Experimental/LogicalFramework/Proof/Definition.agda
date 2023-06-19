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

  -- Introduction and elimination for logical combinators ⊤ᵇ, ⊥ᵇ, ⊃, ∧ and ∀
  ⊤ᵇ-intro : Proof Γ  -- Ξ ⊢ ⊤ᵇ
  ⊥ᵇ-elim : Proof Γ  -- Ξ ⊢ ⊥ᵇ ⊃ φ
  ⊃-intro : (x : String) →
            Proof Γ  -- Ξ ,,ᵇ μ ∣ x ∈ φ ⊢ ψ
            →
            Proof Γ  -- Ξ ⊢ ⟨ μ ∣ φ ⟩⊃ ψ
  ⊃-elim : (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) →
           Proof Γ →             -- Ξ ⊢ ⟨ μ ∣ φ ⟩⊃ ψ
           Proof (Γ ,lock⟨ μ ⟩)  -- Ξ ,lock⟨ μ ⟩ ⊢ φ
           →
           Proof Γ               -- Ξ ⊢ ψ
  assumption' : (x : String) {μ κ : Modality m n} (α : TwoCell μ κ) → Proof Γ
  ∧-intro : Proof Γ →  -- Ξ ⊢ φ
            Proof Γ     -- Ξ ⊢ ψ
            →
            Proof Γ     -- Ξ ⊢ φ ∧ ψ
  ∧-elimˡ : (ψ : bProp Γ) →
            Proof Γ  -- Ξ ⊢ φ ∧ ψ
            →
            Proof Γ  -- Ξ ⊢ φ
  ∧-elimʳ : (φ : bProp Γ) →
            Proof Γ  -- Ξ ⊢ φ ∧ ψ
            →
            Proof Γ  -- Ξ ⊢ ψ
  ∀-intro[_∣_∈_]_ : (μ : Modality n m) (x : String) (T : Ty n) → Proof (Γ ,, μ ∣ x ∈ T) → Proof Γ
  ∀-elim : (μ : Modality n m) (φ : bProp Γ) → Proof Γ → (t : Tm (Γ ,lock⟨ μ ⟩) T) → Proof Γ

  -- Modal reasoning principles
  mod⟨_⟩_ : (μ : Modality n m) →
            Proof (Γ ,lock⟨ μ ⟩)  -- Ξ ,lock⟨ μ ⟩ ⊢ φ
            →
            Proof Γ               -- Ξ ⊢ ⟨ μ ∣ φ ⟩
  mod-elim : (ρ : Modality n m) (μ : Modality o n) (x : String) (φ : bProp (Γ ,lock⟨ ρ ⟩ ,lock⟨ μ ⟩)) →
             Proof (Γ ,lock⟨ ρ ⟩) →  -- Ξ ,lock⟨ ρ ⟩ ⊢ ⟨ μ ∣ φ ⟩
             Proof Γ                 -- Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ ⊢ ψ
             →
             Proof Γ                 -- Ξ ⊢ ψ

  -- Specific computation rules for term formers
  fun-β : Proof Γ
  nat-rec-β-zero : Proof Γ
  nat-rec-β-suc : Proof Γ

  {-
  -- postponed, should be handled by the normalizer
  if-β-true : {t f : Tm (to-ctx Ξ) T} →
              (Ξ ⊢ if true t f ≡ᵇ t)
  if-β-false : {t f : Tm (to-ctx Ξ) T} →
               (Ξ ⊢ if false t f ≡ᵇ f)
  pair-β-fst : {t : Tm (to-ctx Ξ) T} {s : Tm (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᵇ t)
  pair-β-snd : {t : Tm (to-ctx Ξ) T} {s : Tm (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᵇ s)
  -}
  fun-η : String → Proof Γ  -- Ξ ⊢ f ≡ᵇ lam[ μ ∣ x ∈ T ] (weaken-tm f ∙ svar "x")
  ⊠-η : Proof Γ  -- Ξ ⊢ p ≡ᵇ pair (fst p) (snd p)

  -- Axioms specifying distinctness of booleans and natural numbers
  true≠false : Proof Γ  -- Ξ ⊢ ¬ (true ≡ᵇ false)
  suc-inj : (x y : String) → Proof Γ  -- Ξ ⊢ ∀[ 𝟙 ∣ x ∈ Nat' ] ∀[ 𝟙 ∣ y ∈ Nat' ] (suc ∙ (svar x) ≡ᵇ suc ∙ (svar y)) ⊃ (svar x ≡ᵇ svar y)
  zero≠sucn : (x : String) → Proof Γ  -- Ξ ⊢ ∀[ 𝟙 ∣ x ∈ Nat' ] ¬ (zero ≡ᵇ suc ∙ svar x)

  {-
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
