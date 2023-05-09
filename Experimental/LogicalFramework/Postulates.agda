-- This module lists all axioms that are currently postulated.
-- They should eventually be proved.

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.Postulates
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Data.String using (String)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M
import Model.Type.Function as M

open ModeTheory ℳ
open ModeTheoryInterpretation ⟦ℳ⟧

open import Experimental.LogicalFramework.MSTT ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.bProp ℳ ⟦ℳ⟧
import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ as Syn

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n


postulate
  tm-sub-sound : (t : Tm Δ T) (σ : Sub Γ Δ) → ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧sub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
  bprop-sub-sound : (φ : bProp Δ) (σ : Sub Γ Δ) → ⟦ φ ⟧bprop M.[ ⟦ σ ⟧sub ] M.≅ᵗʸ ⟦ φ [ σ ]bprop ⟧bprop

  unlock𝟙-bprop-sound : (φ : bProp (Γ ,lock⟨ 𝟙 ⟩)) → ⟦ unlock𝟙-bprop φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop
  unfuselocks-bprop-sound : {μ : Modality n o} {ρ : Modality m n} (φ : bProp (Γ ,lock⟨ μ ⓜ ρ ⟩)) →
                            ⟦ unfuselocks-bprop {μ = μ} φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop M.[ M.to (M.eq-lock (⟦ⓜ⟧-sound μ ρ) _) ]

  key-sub-sound : {μ ρ : Modality m n} (α : TwoCell μ ρ) {Γ : Ctx n} →
                  M.key-subst ⟦ α ⟧two-cell M.≅ˢ ⟦ key-sub {Γ = Γ} (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ μ ⟩) α ⟧sub
  sub-lock-sound : (σ : Sub Γ Δ) (μ : Modality m n) → ⟦ σ ,slock⟨ μ ⟩ ⟧sub M.≅ˢ M.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧sub
  sub-π-sound : {Γ : Ctx m} {x : String} {μ : Modality n m} {T : Ty n} → ⟦ π {Γ = Γ} {μ = μ} {x} {T} ⟧sub M.≅ˢ M.π
  /-sound : {Γ : Ctx m} {μ : Modality n m} {T : Ty n} (t : Tm (Γ ,lock⟨ μ ⟩) T) (x : String) →
            ⟦ t / x ⟧sub M.≅ˢ M.id-subst _ M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm

atomic-rename-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (σ : AtomicRen.AtomicRen Δ Γ) →
                  ⟦ AtomicRen.atomic-rename-tm t σ ⟧tm M.≅ᵗᵐ (⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl )
atomic-rename-tm-sound  σ = {!!}

rename-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (σ : Ren Δ Γ) →
                  ⟦ rename-tm t σ ⟧tm M.≅ᵗᵐ (⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧ren ]cl )
rename-tm-sound  {μ} {m} {Γ} {T} t Syn.RenSub.id =
  M.symᵗᵐ (M.cl-tm-subst-id (ty-closed-natural T) ⟦ t ⟧tm)
rename-tm-sound {Γ = Γ} {T = T} t (σs ⊚a σ) = M.transᵗᵐ step3 (M.transᵗᵐ step1 step2)
  where step0 : ⟦ rename-tm t σs ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren ]cl
        step0 = rename-tm-sound t σs
        step1 : ⟦ rename-tm t σs ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl M.≅ᵗᵐ
                ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren ]cl M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl
        step1 = M.cl-tm-subst-cong-tm (ty-closed-natural T) step0
        step2 : ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren ]cl M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl  M.≅ᵗᵐ
                ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren M.⊚ ⟦ σ ⟧aren ]cl
        step2 = M.cl-tm-subst-⊚ (ty-closed-natural T) ⟦ t ⟧tm
        step3 : ⟦ AtomicRen.atomic-rename-tm (rename-tm t σs) σ ⟧tm M.≅ᵗᵐ
                  ⟦ rename-tm t σs ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl
        step3 = atomic-rename-tm-sound (rename-tm t σs) σ

lock𝟙-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) → ⟦ lock𝟙-tm t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm
lock𝟙-sound t = M.transᵗᵐ (rename-tm-sound t lock𝟙-ren)
  {! !}

∙¹-sound : {Γ : Ctx m} {A B : Ty m} (f : Tm Γ (A ⇛ B)) (a : Tm Γ A) →
           ⟦ f ∙¹ a ⟧tm M.≅ᵗᵐ M.app ⟦ f ⟧tm ⟦ a ⟧tm
∙¹-sound f a = M.app-cong M.reflᵗᵐ (lock𝟙-sound a)
