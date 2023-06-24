-- This module lists all axioms that are currently postulated.
-- They should eventually be proved.

{-# OPTIONS --allow-unsolved-metas #-}

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

module Experimental.LogicalFramework.Postulates (ℳ : ModeTheory) where

open import Data.String using (String)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M
import Model.Type.Function as M

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT ℳ
open import Experimental.LogicalFramework.bProp ℳ
import Experimental.LogicalFramework.MSTT.Syntax.Named ℳ as Syn

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n


postulate
  tm-sub-sound : (t : Tm Δ T) (σ : Sub Γ Δ) → ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧sub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
  bprop-sub-sound : (φ : bProp Δ) (σ : Sub Γ Δ) → ⟦ φ ⟧bprop M.[ ⟦ σ ⟧sub ] M.≅ᵗʸ ⟦ φ [ σ ]bprop ⟧bprop

  v0-sound : (Γ : Ctx n) (μ : Modality m n) (x : String) (T : Ty m) →
             ⟦ v0 {Γ = Γ} {μ = μ} {x} {T} ⟧tm M.≅ᵗᵐ M.mod-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
  v0-𝟙-sound : (Γ : Ctx m) (x : String) (T : Ty m) →
               ⟦ v0-𝟙 {Γ = Γ} {x = x} {T = T} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T)
  v1-sound : (Γ : Ctx n) (μ : Modality m n) (x : String) (T : Ty m) (κ : Modality o n) (y : String) (S : Ty o) →
             ⟦ v1 {Γ = Γ} {μ = μ} {x} {T} {κ = κ} {y} {S} ⟧tm
               M.≅ᵗᵐ
             M.mod-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩) M.[ ty-closed-natural ⟨ μ ∣ T ⟩ ∣ M.π ]cl)
  v1-𝟙-sound : (Γ : Ctx m) (x : String) (T : Ty m) (κ : Modality n m) (y : String) (S : Ty n) →
               ⟦ v1-𝟙 {Γ = Γ} {x = x} {T} {_} {κ} {y} {S} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T) M.[ ty-closed-natural T ∣ M.π ]cl

  lock𝟙-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) → ⟦ lock𝟙-tm t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm

  unlock𝟙-bprop-sound : (φ : bProp (Γ ,lock⟨ 𝟙 ⟩)) → ⟦ unlock𝟙-bprop φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop
  lock𝟙-bprop-sound : (φ : bProp Γ) → ⟦ lock𝟙-bprop φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop
  unfuselocks-bprop-sound : {μ : Modality n o} {ρ : Modality m n} (φ : bProp (Γ ,lock⟨ μ ⓜ ρ ⟩)) →
                            ⟦ unfuselocks-bprop {μ = μ} φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop M.[ M.to (M.eq-lock (⟦ⓜ⟧-sound μ ρ) _) ]
  fuselocks-bprop-sound : {μ : Modality n o} {ρ : Modality m n} (φ : bProp (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)) →
                          ⟦ fuselocks-bprop φ ⟧bprop M.[ M.to (M.eq-lock (⟦ⓜ⟧-sound μ ρ) _) ] M.≅ᵗʸ ⟦ φ ⟧bprop

  ren-π-sound : (Γ : Ctx m) (x : String) (μ : Modality n m) (T : Ty n) → ⟦ π-ren {Γ = Γ} {μ = μ} {x} {T} ⟧ren M.≅ˢ M.π

  key-sub-sound : {μ ρ : Modality m n} (α : TwoCell μ ρ) {Γ : Ctx n} →
                  M.key-subst ⟦ α ⟧two-cell M.≅ˢ ⟦ key-sub {Γ = Γ} (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ μ ⟩) α ⟧sub
  sub-lock-sound : (σ : Sub Γ Δ) (μ : Modality m n) → ⟦ σ ,slock⟨ μ ⟩ ⟧sub M.≅ˢ M.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧sub
  sub-π-sound : (Γ : Ctx m) (x : String) (μ : Modality n m) (T : Ty n) → ⟦ π {Γ = Γ} {μ = μ} {x} {T} ⟧sub M.≅ˢ M.π
  /cl-sound : {Γ : Ctx m} {μ : Modality n m} {T : Ty n} (t : Tm (Γ ,lock⟨ μ ⟩) T) (x : String) →
              ⟦ t / x ⟧sub M.≅ˢ (M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm) M./cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩
  ∷ˢ-sound : (σ : Sub Γ Δ) {μ : Modality m n} (t : Tm (Γ ,lock⟨ μ ⟩) T) (x : String) →
             ⟦ σ ∷ˢ t / x ⟧sub M.≅ˢ ⟦ σ ⟧sub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm

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
∙¹-sound f a = M.app-cong M.reflᵗᵐ (lock𝟙-tm-sound a)

/v-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (x : String) →
           ⟦ lock𝟙-tm t / x ⟧sub M.≅ˢ (⟦ t ⟧tm M./v)
/v-sound {T = T} t x =
  M.transˢ (/cl-sound (lock𝟙-tm t) x) (
  M.transˢ (M.,cl-cong-tm (ty-closed-natural ⟨ 𝟙 ∣ T ⟩) (lock𝟙-tm-sound t)) (
  M.transˢ (M.,cl-cong-cl (M.𝟙-preserves-cl (ty-closed-natural T))) (
  M.symˢ (M./v-/cl (ty-closed-natural T) ⟦ t ⟧tm))))

weaken-tm-sound : (Γ : Ctx m) (x : String) (μ : Modality n m) (S : Ty n) {T : Ty m} (t : Tm Γ T) →
                  ⟦ weaken-tm {μ = μ} {x} {S} t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.π ]cl
weaken-tm-sound Γ x μ S {T} t = M.transᵗᵐ (rename-tm-sound t π-ren) (M.cl-tm-subst-cong-subst (ty-closed-natural T) (ren-π-sound Γ x μ S))

v0-sound-𝟙 : (Γ : Ctx m) (x : String) (T : Ty m) →
             ⟦ v0 {Γ = Γ} {μ = 𝟙} {x = x} {T = T} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T)
v0-sound-𝟙 Γ x T = M.transᵗᵐ (v0-sound Γ 𝟙 x T) (M.ξcl-cong-cl (M.𝟙-preserves-cl (ty-closed-natural T)))

v1-sound-𝟙 : (Γ : Ctx m) (x : String) (T : Ty m) (κ : Modality n m) (y : String) (S : Ty n) →
             ⟦ v1 {Γ = Γ} {μ = 𝟙} {x} {T} {κ = κ} {y} {S} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T) M.[ ty-closed-natural T ∣ M.π ]cl
v1-sound-𝟙 Γ x T κ y S =
  M.transᵗᵐ (v1-sound Γ 𝟙 x T κ y S) (
  M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.𝟙-preserves-cl (ty-closed-natural T))) (
  M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.ξcl-cong-cl (M.𝟙-preserves-cl (ty-closed-natural T)))))
