--------------------------------------------------
-- Definition of proofs
--------------------------------------------------

open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof.Definition
  (ℬ : BiSikkelParameter)
  where

open import Data.List
open import Data.Product
open import Data.String as Str using (String)
open import Data.Unit
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open BiSikkelParameter ℬ

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷
open import Experimental.LogicalFramework.Parameter.ProofExtension 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯

open ProofExt 𝓅

open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : Name


data Proof : {m : Mode} → Ctx m → Set
ExtPfArgs : {m : Mode} (pfarg-infos : List (ArgInfo m)) → ArgBoundNames pfarg-infos → Ctx m → Set

data Proof where
  {-
  TODO: Primitive for applying a 2-cell to a proof (and consequently also to the prosposition it proves).
        This would subsume all constructors below.
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

  -- Integration of normalization procedure in proofs
  with-normalization : Proof Γ → Proof Γ

  -- Expanding definitions of MSTT terms
  by-unfold-global-def : Proof Γ  -- Ξ ⊢ def _ {t} ≡ᵇ t

  -- Introduction and elimination for logical combinators ⊤ᵇ, ⊥ᵇ, ⊃, ∧ and ∀
  ⊤ᵇ-intro : Proof Γ  -- Ξ ⊢ ⊤ᵇ
  ⊥ᵇ-elim : Proof Γ  -- Ξ ⊢ ⊥ᵇ
            →
            Proof Γ  -- Ξ ⊢ φ
  ⊃-intro : (x : Name) →
            Proof Γ  -- Ξ ,,ᵇ μ ∣ x ∈ φ ⊢ ψ
            →
            Proof Γ  -- Ξ ⊢ ⟨ μ ∣ φ ⟩⊃ ψ
  ⊃-elim : (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) →
           Proof Γ →             -- Ξ ⊢ ⟨ μ ∣ φ ⟩⊃ ψ
           Proof (Γ ,lock⟨ μ ⟩)  -- Ξ ,lock⟨ μ ⟩ ⊢ φ
           →
           Proof Γ               -- Ξ ⊢ ψ
  assumption' : {m n : Mode} {Γ : Ctx m} (x : Name) {μ κ : Modality m n} (α : TwoCell μ κ) → Proof Γ
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
  ∀-intro[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) →
                    Proof (Γ ,, μ ∣ x ∈ T)  -- Ξ ,,ᵛ μ ∣ x ∈ T ⊢ φ
                    →
                    Proof Γ                 -- Ξ ⊢ ∀[ μ ∣ x ∈ T ] φ
  ∀-elim : (μ : Modality n m) (φ : bProp Γ) →
           Proof Γ →                  -- Ξ ⊢ ∀[ μ ∣ x ∈ T ] φ
           (t : Tm (Γ ,lock⟨ μ ⟩) T)  -- to-ctx Ξ ,lock⟨ μ ⟩ ⊢ t : T
           →
           Proof Γ                    -- Ξ ⊢ φ [ t / x ]bprop

  -- Modal reasoning principles
  mod⟨_⟩_ : (μ : Modality n m) →
            Proof (Γ ,lock⟨ μ ⟩)  -- Ξ ,lock⟨ μ ⟩ ⊢ φ
            →
            Proof Γ               -- Ξ ⊢ ⟨ μ ∣ φ ⟩
  mod-elim : (ρ : Modality n m) (μ : Modality o n) (x : Name) (φ : bProp (Γ ,lock⟨ ρ ⟩ ,lock⟨ μ ⟩)) →
             Proof (Γ ,lock⟨ ρ ⟩) →  -- Ξ ,lock⟨ ρ ⟩ ⊢ ⟨ μ ∣ φ ⟩
             Proof Γ                 -- Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ ⊢ ψ
             →
             Proof Γ                 -- Ξ ⊢ ψ

  fun-η : Name → Proof Γ  -- Ξ ⊢ f ≡ᵇ lam[ μ ∣ x ∈ T ] (weaken-tm f ∙ svar "x")
  ⊠-η : Proof Γ  -- Ξ ⊢ p ≡ᵇ pair (fst p) (snd p)

  -- Axioms specifying distinctness of booleans and natural numbers
  true≠false : Proof Γ  -- Ξ ⊢ ¬ (true ≡ᵇ false)
  suc-inj : (x y : Name) → Proof Γ  -- Ξ ⊢ ∀[ 𝟙 ∣ x ∈ Nat' ] ∀[ 𝟙 ∣ y ∈ Nat' ] (suc (svar x) ≡ᵇ suc (svar y)) ⊃ (svar x ≡ᵇ svar y)
  zero≠sucn : (x : Name) → Proof Γ  -- Ξ ⊢ ∀[ 𝟙 ∣ x ∈ Nat' ] ¬ (zero ≡ᵇ suc (svar x))

  -- Induction schemata for Bool' and Nat'
  bool-induction' : {Γ Δ : Ctx m} {x : Name} → Δ Ag.≡ (Γ ,, x ∈ Bool') →
                    Proof Γ →  -- Ξ ⊢ φ [ true  / x ]bprop
                    Proof Γ     -- Ξ ⊢ φ [ false / x ]bprop
                    →
                    Proof Δ     -- Ξ ,,ᵛ x ∈ Bool' ⊢ φ
    -- ^ We cannot just return a proof of type Proof (Γ ,, x ∈ Nat')
    -- because in that case pattern matching in the proof checker
    -- would fail. Users are intended to use bool-induction defined below.
  nat-induction' : {Γ Δ : Ctx m} {x : Name} (hyp : String) → Δ Ag.≡ (Γ ,, x ∈ Nat') →
                   Proof Γ →  -- Ξ ⊢ φ [ zero / x ]bprop
                   Proof Δ     -- Ξ ,,ᵛ n ∈ Nat' ,,ᵇ 𝟙 ∣ hyp ∈ φ ⊢ φ [ suc n / n ]bprop
                   →
                   Proof Δ     -- Ξ ,,ᵛ n ∈ Nat' ⊢ φ
    -- ^ Same remark as for bool-induction'.

  -- Dependent eliminator for modal types
  mod-induction' : {Γ Δ : Ctx m} (κ : Modality o n) (μ : Modality n m) (x : Name) {y : Name} →
                   Δ Ag.≡ (Γ ,, μ ∣ y ∈ ⟨ κ ∣ T ⟩) →
                                               -- φ : bProp (Γ ,, μ ∣ y ∈ ⟨ κ ∣ T ⟩)
                   Proof (Γ ,, μ ⓜ κ ∣ x ∈ T)  -- Ξ ,,ᵛ μ ⓜ κ ∣ x ∈ T ⊢ φ [ mod⟨ κ ⟩ x / y ]bprop
                   →
                   Proof Δ                     -- Ξ ,,ᵛ μ ∣ y ∈ ⟨ κ ∣ T ⟩ ⊢ φ

  fun-cong : Proof Γ → Tm (Γ ,lock⟨ μ ⟩) T → Proof Γ
  cong : {T S : Ty m} → Tm Γ (⟨ μ ∣ T ⟩⇛ S) → Proof (Γ ,lock⟨ μ ⟩) → Proof Γ

  -- Extras: holes in proofs and custom extensions of the proof system
  hole : String → Proof Γ
  ext : (c : ProofExtCode m) {Γ : Ctx m} →
        (tmarg-names : TmArgBoundNames (pf-code-tmarg-infos c)) → ExtTmArgs (pf-code-tmarg-infos c) tmarg-names Γ →
        (bparg-names : ArgBoundNames (pf-code-bparg-infos c)) → ExtBPArgs (pf-code-bparg-infos c) bparg-names Γ →
        (pfarg-names : ArgBoundNames (pf-code-pfarg-infos c)) →
        ExtPfArgs (pf-code-pfarg-infos c) pfarg-names Γ →
        Proof Γ

ExtPfArgs []             _                        Γ = ⊤
ExtPfArgs (info ∷ infos) (arg-names , args-names) Γ =
  Proof (Γ ++tel (add-names (arg-tel info) arg-names)) × ExtPfArgs infos args-names Γ


by-normalization : Proof Γ
by-normalization = with-normalization refl

-- More useful versions of the induction principles for Bool', Nat'
-- and modal types.
bool-induction : {Γ : Ctx m} {x : String} →
                 Proof Γ → Proof Γ → Proof (Γ ,, x ∈ Bool')
bool-induction = bool-induction' Ag.refl

nat-induction : {Γ : Ctx m} {x : String} (hyp : String) →
                Proof Γ → Proof (Γ ,, x ∈ Nat') → Proof (Γ ,, x ∈ Nat')
nat-induction hyp = nat-induction' hyp Ag.refl

mod-induction : {Γ : Ctx m} (κ : Modality o n) (μ : Modality n m) (x : Name) {y : Name} →
                Proof (Γ ,, μ ⓜ κ ∣ x ∈ T) → Proof (Γ ,, μ ∣ y ∈ ⟨ κ ∣ T ⟩)
mod-induction κ μ x = mod-induction' κ μ x Ag.refl


-- Equational reasoning with BiSikkel proofs
module ≡ᵇ-Reasoning where

  infix 1 begin_
  infixr 2 _≡ᵇ⟨_⟩_ _≡ᵇ⟨⟩_ _≡ᵇ⟨_⟨_
  infix 3 _∎

  begin_ : (Tm Γ T × Proof Γ) → Proof Γ
  begin (_ , p) = p

  _≡ᵇ⟨_⟩_ : Tm Γ T → Proof Γ → (Tm Γ T × Proof Γ) → (Tm Γ T × Proof Γ)
  t ≡ᵇ⟨ t=s ⟩ (s , s=r) = t , trans s t=s s=r

  _≡ᵇ⟨⟩_ : Tm Γ T → (Tm Γ T × Proof Γ) → (Tm Γ T × Proof Γ)
  t ≡ᵇ⟨⟩ (s , s=r) = t , s=r

  _≡ᵇ⟨_⟨_ : Tm Γ T → Proof Γ → (Tm Γ T × Proof Γ) → (Tm Γ T × Proof Γ)
  t ≡ᵇ⟨ s=t ⟨ (s , s=r) = t , (trans s (sym s=t) s=r)

  _∎ : Tm Γ T → (Tm Γ T × Proof Γ)
  t ∎ = t , refl
