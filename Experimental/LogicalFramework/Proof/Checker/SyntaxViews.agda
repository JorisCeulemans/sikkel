open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.Proof.Checker.SyntaxViews
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n : Mode
  Γ : Ctx m
  T S : Ty m


data IsEquation : bProp Γ → Set where
  is-eq : (t1 t2 : Tm Γ T) → IsEquation (t1 ≡ᵇ t2)

is-eq? : (φ : bProp Γ) → PCM (IsEquation φ)
is-eq? (t1 ≡ᵇ t2) = return (is-eq t1 t2)
is-eq? φ = throw-error "bProp is not an equation"

data IsForall : bProp Γ → Set where
  is-forall : {Γ : Ctx m} (μ : Modality n m) (x : Name) (T : Ty n) (φ : bProp (Γ ,, μ ∣ x ∈ T)) →
              IsForall (∀[ μ ∣ x ∈ T ] φ)

is-forall? : (φ : bProp Γ) → PCM (IsForall φ)
is-forall? (∀[ μ ∣ x ∈ T ] φ) = return (is-forall μ x T φ)
is-forall? φ = throw-error "bProp is not of the form ∀ x ..."

data IsImplication : bProp Γ → Set where
  is-implication : {Γ : Ctx m} (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) (ψ : bProp Γ) →
                   IsImplication (⟨ μ ∣ φ ⟩⊃ ψ)

is-implication? : (φ : bProp Γ) → PCM (IsImplication φ)
is-implication? (⟨ μ ∣ φ ⟩⊃ ψ) = return (is-implication μ φ ψ)
is-implication? φ = throw-error "bProp is not of the form ⟨ μ ∣ φ ⟩⊃ ψ."

data IsConjunction : bProp Γ → Set where
  is-conjunction : {Γ : Ctx m} (φ ψ : bProp Γ) → IsConjunction (φ ∧ ψ)

is-conjunction? : (φ : bProp Γ) → PCM (IsConjunction φ)
is-conjunction? (φ ∧ ψ) = return (is-conjunction φ ψ)
is-conjunction? _ = throw-error "bProp is not of the form φ ∧ ψ."

data IsModalProp : bProp Γ → Set where
  is-modal : {Γ : Ctx m} (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) →
             IsModalProp ⟨ μ ∣ φ ⟩

is-modal? : (φ : bProp Γ) → PCM (IsModalProp φ)
is-modal? ⟨ μ ∣ φ ⟩ = return (is-modal μ φ)
is-modal? _ = throw-error "bProp is not of the form ⟨ μ ∣ φ ⟩."


data IsLam : Tm Γ T → Set where
  lam : (μ : Modality n m) (x : Name) (b : Tm (Γ ,, μ ∣ x ∈ T) S) → IsLam (lam[ μ ∣ x ∈ T ] b)

is-lam? : (t : Tm Γ T) → PCM (IsLam t)
is-lam? (lam[ μ ∣ x ∈ T ] b) = return (lam μ x b)
is-lam? _ = throw-error "Lambda expected"

data IsApp : Tm Γ T → Set where
  app : {μ : Modality m n} (f : Tm Γ (⟨ μ ∣ T ⟩⇛ S)) (t : Tm (Γ ,lock⟨ μ ⟩) T) → IsApp (f ∙ t)

is-app? : (t : Tm Γ T) → PCM (IsApp t)
is-app? (f ∙ t) = return (app f t)
is-app? _ = throw-error "Function application expected"

data IsNatRec : Tm Γ T → Set where
  nat-rec : ∀ {A} (z : Tm Γ A) (s : Tm Γ (A ⇛ A)) (n : Tm Γ Nat') → IsNatRec (nat-rec z s n)

is-nat-rec? : (t : Tm Γ T) → PCM (IsNatRec t)
is-nat-rec? (nat-rec z s n) = return (nat-rec z s n)
is-nat-rec? _ = throw-error "Natural number recursor expected"

data IsSucTm : Tm Γ T → Set where
  suc-tm : (n : Tm Γ Nat') → IsSucTm (suc n)

is-suc-tm? : (t : Tm Γ T) → PCM (IsSucTm t)
is-suc-tm? (suc n) = return (suc-tm n)
is-suc-tm? _ = throw-error "successor of natural number expected"

data IsGlobalDef : Tm Γ T → Set where
  global-def : {Γ : Ctx m} (name : DefName) (t : Tm ◇ T) → IsGlobalDef {Γ = Γ} (global-def name {t})

is-global-def? : (t : Tm Γ T) → PCM (IsGlobalDef t)
is-global-def? (global-def name {t}) = return (global-def name t)
is-global-def? _ = throw-error "Tried to expand a definition, but no definition is present."


data IsFunTy : Ty m → Set where
  is-fun-ty : (μ : Modality n m) (T : Ty n) (S : Ty m) → IsFunTy (⟨ μ ∣ T ⟩⇛ S)

is-fun-ty? : (T : Ty m) → PCM (IsFunTy T)
is-fun-ty? (⟨ μ ∣ T ⟩⇛ S) = return (is-fun-ty μ T S)
is-fun-ty? _  = throw-error "Function type expected"

data IsProdTy : Ty m → Set where
  is-prod-ty : (T S : Ty m) → IsProdTy (T ⊠ S)

is-prod-ty? : (T : Ty m) → PCM (IsProdTy T)
is-prod-ty? (T ⊠ S) = return (is-prod-ty T S)
is-prod-ty? _  = throw-error "Product type expected"


data EndsInProgVar : ProofCtx m → Set where
  ends-in-prog-var : (Ξ : ProofCtx m) (μ : Modality n m) (x : Name) (T : Ty n) → EndsInProgVar (Ξ ,,ᵛ μ ∣ x ∈ T)

ends-in-prog-var? : (Ξ : ProofCtx m) → PCM (EndsInProgVar Ξ)
ends-in-prog-var? (Ξ ,,ᵛ μ ∣ x ∈ T) = return (ends-in-prog-var Ξ μ x T)
ends-in-prog-var? _ = throw-error "Expected variable at head of proof context."
