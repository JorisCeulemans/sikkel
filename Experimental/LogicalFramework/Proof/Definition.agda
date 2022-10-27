--------------------------------------------------
-- Definition of proof contexts and proofs
--------------------------------------------------

module Experimental.LogicalFramework.Proof.Definition where

open import Data.String as Str hiding (_≟_)
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open import Experimental.LogicalFramework.MSTT
open import Experimental.LogicalFramework.Formula

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : Formula Γ
  x y : String


-- A proof context can, apart from MSTT variables, also consist of formulas (assumptions).
data ProofCtx (m : Mode) : Set
to-ctx : ProofCtx m → Ctx m

infixl 2 _,,ᵛ_∣_∈_ _,,ᶠ_∣_∈_
data ProofCtx m where
  [] : ProofCtx m
  _,,ᵛ_∣_∈_ : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (T : Ty n) → ProofCtx m
  _,,ᶠ_∣_∈_ : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (φ : Formula ((to-ctx Ξ) ,lock⟨ μ ⟩)) → ProofCtx m
  _,lock⟨_⟩ : (Ξ : ProofCtx n) (μ : Modality m n) → ProofCtx m

to-ctx []               = ◇
to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T) = (to-ctx Ξ) ,, μ ∣ x ∈ T
to-ctx (Ξ ,,ᶠ _ ∣ _ ∈ _) = to-ctx Ξ
to-ctx (Ξ ,lock⟨ μ ⟩)   = (to-ctx Ξ) ,lock⟨ μ ⟩

private variable
  Ξ : ProofCtx m


-- In the same way as variables in MSTT, assumptions are internally
--  referred to using De Bruijn indices, but we keep track of their
--  names. The (proof-relevant) predicate Assumption x μ κ Ξ expresses
--  that an assumption with name x is present in proof context Ξ under
--  modality μ and with κ the composition of all locks to the right of
--  x. Note that we do not keep track of the formula in the Assumption
--  type (in contrast to the type of variables in MSTT).
data Assumption (x : String) (μ : Modality n o) : Modality m o → ProofCtx m → Set where
  azero : Assumption x μ 𝟙 (Ξ ,,ᶠ μ ∣ x ∈ φ)
  asuc  : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᶠ ρ ∣ y ∈ ψ)
  skip-var : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᵛ ρ ∣ y ∈ T)
  skip-lock : (ρ : Modality m p) → Assumption x μ κ Ξ → Assumption x μ (κ ⓜ ρ) (Ξ ,lock⟨ ρ ⟩)

lookup-assumption' : Assumption x μ κ Ξ → (ρ : Modality _ _) →
                     TwoCell μ (κ ⓜ ρ) → Formula ((to-ctx Ξ) ,lock⟨ ρ ⟩)
lookup-assumption' (azero {φ = φ}) ρ α = φ [ key-sub (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ _ ⟩) (Ag.subst (λ - → TwoCell - _) (Ag.sym mod-unitˡ) α) ]frm
lookup-assumption' (asuc a) ρ α = lookup-assumption' a ρ α
lookup-assumption' (skip-var a) ρ α = (lookup-assumption' a ρ α) [ π ,slock⟨ ρ ⟩ ]frm
lookup-assumption' (skip-lock {κ = κ} ρ' a) ρ α = unfuselocks-frm (lookup-assumption' a (ρ' ⓜ ρ) (Ag.subst (TwoCell _) (mod-assoc {μ = κ}) α))

lookup-assumption : Assumption x μ κ Ξ → TwoCell μ κ → Formula (to-ctx Ξ)
lookup-assumption a α = unlock𝟙-frm (lookup-assumption' a 𝟙 (Ag.subst (TwoCell _) (Ag.sym mod-unitʳ) α))


data Proof {m : Mode} : ProofCtx m → Set where
  {-
  -- Functoriality of the locks in a proof context
  lock𝟙-der : (Ξ ⊢ φ) → (Ξ ,lock⟨ 𝟙 ⟩ ⊢ lock𝟙-frm φ)
  unlock𝟙-der : (Ξ ,lock⟨ 𝟙 ⟩ ⊢ φ) → (Ξ ⊢ unlock𝟙-frm φ)
  fuselocks-der : (Ξ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩ ⊢ φ) → (Ξ ,lock⟨ μ ⓜ ρ ⟩ ⊢ fuselocks-frm φ)
  unfuselocks-der : (Ξ ,lock⟨ μ ⓜ ρ ⟩ ⊢ φ) → (Ξ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩ ⊢ unfuselocks-frm φ)
  -}

  -- Structural rules for ≡ᶠ
  refl : Proof Ξ
  sym : Proof Ξ → Proof Ξ
  trans : (middle-tm : Tm (to-ctx Ξ) T) →
          Proof Ξ → Proof Ξ → Proof Ξ
  {-
  subst : (φ : Formula (to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T))) {t1 t2 : Tm (to-ctx (Ξ ,lock⟨ μ ⟩)) T} →
          (Ξ ,lock⟨ μ ⟩ ⊢ t1 ≡ᶠ t2) →
          (Ξ ⊢ φ [ t1 / x ]frm) →
          (Ξ ⊢ φ [ t2 / x ]frm)

  -- Introduction and elimination for logical combinators ⊤ᶠ, ⊥ᶠ, ⊃, ∧ and ∀
  ⊤ᶠ-intro : Ξ ⊢ ⊤ᶠ
  ⊥ᶠ-elim : Ξ ⊢ ⊥ᶠ ⊃ φ
  assume[_∣_]_ : (μ : Modality m n) {φ : Formula ((to-ctx Ξ) ,lock⟨ μ ⟩)} (x : String) →
                 (Ξ ,,ᶠ μ ∣ x ∈ φ ⊢ ψ) →
                 (Ξ ⊢ ⟨ μ ∣ φ ⟩ ⊃ ψ)
  ⊃-elim : (Ξ ⊢ ⟨ μ ∣ φ ⟩ ⊃ ψ) → (Ξ ,lock⟨ μ ⟩ ⊢ φ) → (Ξ ⊢ ψ)
  -}
  assumption' : (x : String) {μ κ : Modality m n} {Ξ : ProofCtx m} (a : Assumption x μ κ Ξ) (α : TwoCell μ κ) → Proof Ξ
  {-
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  -}
  ∀-intro[_∣_∈_]_ : (μ : Modality n m) (x : String) (T : Ty n) → Proof (Ξ ,,ᵛ μ ∣ x ∈ T) → Proof Ξ
  ∀-elim : (μ : Modality n m) (φ : Formula (to-ctx Ξ)) → Proof Ξ → (t : Tm ((to-ctx Ξ) ,lock⟨ μ ⟩) T) → Proof Ξ
  {-

  -- Modal reasoning principles
  mod⟨_⟩_ : (μ : Modality m n) {φ : Formula (to-ctx (Ξ ,lock⟨ μ ⟩))} →
            (Ξ ,lock⟨ μ ⟩ ⊢ φ) →
            (Ξ ⊢ ⟨ μ ∣ φ ⟩)
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : String) {φ : Formula _} →
             (Ξ ,lock⟨ ρ ⟩ ⊢ ⟨ μ ∣ φ ⟩) →
             (Ξ ,,ᶠ ρ ⓜ μ ∣ x ∈ fuselocks-frm φ ⊢ ψ) →
             (Ξ ⊢ ψ)
  -}

  -- Specific computation rules for term formers (currently no eta rules)
  fun-β : Proof Ξ
  nat-elim-β-zero : Proof Ξ
  nat-elim-β-suc : Proof Ξ
  {-
  if-β-true : {t f : Tm (to-ctx Ξ) T} →
              (Ξ ⊢ if true t f ≡ᶠ t)
  if-β-false : {t f : Tm (to-ctx Ξ) T} →
               (Ξ ⊢ if false t f ≡ᶠ f)
  pair-β-fst : {t : Tm (to-ctx Ξ) T} {s : Tm (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᶠ t)
  pair-β-snd : {t : Tm (to-ctx Ξ) T} {s : Tm (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᶠ s)

  -- Axioms specifying distinctness of booleans and natural numbers
  true≠false : Ξ ⊢ ¬ (true ≡ᶠ false)
  suc-inj : {Ξ : ProofCtx m} → Ξ ⊢ ∀[ 𝟙 ∣ "m" ∈ Nat' ] ∀[ 𝟙 ∣ "n" ∈ Nat' ] (suc ∙ (svar "m") ≡ᶠ suc ∙ (svar "n")) ⊃ (svar "m" ≡ᶠ svar "n")
  zero≠sucn : Ξ ⊢ ∀[ 𝟙 ∣ "n" ∈ Nat' ] ¬ (zero ≡ᶠ suc ∙ svar "n")

  -- Induction schemata for Bool' and Nat'
  bool-induction : (Ξ ⊢ φ [ true / x ]frm) →
                   (Ξ ⊢ φ [ false / x ]frm) →
                   (Ξ ,,ᵛ μ ∣ x ∈ Bool' ⊢ φ)
  -}
  nat-induction : {Ξ : ProofCtx m} {μ : Modality n m} {x : String} (hyp : String) (φ : Formula (to-ctx Ξ ,, μ ∣ x ∈ Nat')) →
                  Proof Ξ → Proof (Ξ ,,ᵛ μ ∣ x ∈ Nat' ,,ᶠ 𝟙 ∣ hyp ∈ lock𝟙-frm φ) → Proof (Ξ ,,ᵛ μ ∣ x ∈ Nat')

  fun-cong : {Ξ : ProofCtx m} → Proof Ξ → Tm (to-ctx Ξ) T → Proof Ξ
  cong : {Ξ : ProofCtx m} {T S : Ty m} → Tm (to-ctx Ξ) (T ⇛ S) → Proof Ξ → Proof Ξ
  hole : {Ξ : ProofCtx m} → String → Proof Ξ
