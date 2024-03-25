-- This module lists all axioms that are currently postulated.
-- They should eventually be proved.

{-# OPTIONS --allow-unsolved-metas #-}

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
open import Data.String

module Experimental.LogicalFramework.Postulates
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.String using (String)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Model.Type.Function as M

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n


postulate
  tm-sub-sound : (t : Tm Δ T) (σ : Sub Γ Δ) → ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧sub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tmˢ ⟧tm
  bprop-sub-sound : (φ : bProp Δ) (σ : Sub Γ Δ) → ⟦ φ ⟧bprop M.[ ⟦ σ ⟧sub ] M.≅ᵗʸ ⟦ φ [ σ ]bpropˢ ⟧bprop

  v0-sound : (Γ : Ctx n) (μ : Modality m n) (x : String) (T : Ty m) →
             ⟦ v0 {Γ = Γ} {μ = μ} {x} {T} ⟧tm M.≅ᵗᵐ dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
  v0-𝟙-sound : (Γ : Ctx m) (x : String) (T : Ty m) →
               ⟦ v0-𝟙 {Γ = Γ} {x = x} {T = T} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T)
  v0-2lock-sound : (μ : Modality n o) (κ : Modality m n) (x : String) (Γ : Ctx o) (T : Ty m) →
                   ⟦ var' {Γ = Γ ,, μ ⓜ κ ∣ x ∈ T ,lock⟨ μ ⟩ ,lock⟨ κ ⟩} x {vlock (vlock (vzero id-cell))} ⟧tm
                     M.≅ᵗᵐ
                   dra-elim ⟦ κ ⟧mod (dra-elim ⟦ μ ⟧mod (
                     M.ι⁻¹[ eq-dra-ty-closed (⟦ⓜ⟧-sound μ κ) (ty-closed-natural T) ] (M.ξcl (ty-closed-natural ⟨ μ ⓜ κ ∣ T ⟩) {Γ = ⟦ Γ ⟧ctx})))
  v1-sound : (Γ : Ctx n) (μ : Modality m n) (x : String) (T : Ty m) (κ : Modality o n) (y : String) (S : Ty o) →
             ⟦ v1 {Γ = Γ} {μ = μ} {x} {T} {κ = κ} {y} {S} ⟧tm
               M.≅ᵗᵐ
             dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩) M.[ ty-closed-natural ⟨ μ ∣ T ⟩ ∣ M.π ]cl)
  v1-𝟙-sound : (Γ : Ctx m) (x : String) (T : Ty m) (κ : Modality n m) (y : String) (S : Ty n) →
               ⟦ v1-𝟙 {Γ = Γ} {x = x} {T} {_} {κ} {y} {S} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T) M.[ ty-closed-natural T ∣ M.π ]cl

  lock𝟙-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) → ⟦ lock𝟙-tm t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm

  unlock𝟙-bprop-sound : (φ : bProp (Γ ,lock⟨ 𝟙 ⟩)) → ⟦ unlock𝟙-bprop φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop
  lock𝟙-bprop-sound : (φ : bProp Γ) → ⟦ lock𝟙-bprop φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop
  unfuselocks-bprop-sound : {μ : Modality n o} {ρ : Modality m n} (φ : bProp (Γ ,lock⟨ μ ⓜ ρ ⟩)) →
                            ⟦ unfuselocks-bprop {ρ = ρ} φ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop M.[ M.to (lock-iso (⟦ⓜ⟧-sound μ ρ)) ]
  fuselocks-bprop-sound : {μ : Modality n o} {ρ : Modality m n} (φ : bProp (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)) →
                          ⟦ fuselocks-bprop φ ⟧bprop M.[ M.to (lock-iso (⟦ⓜ⟧-sound μ ρ)) ] M.≅ᵗʸ ⟦ φ ⟧bprop

  ren-key-sound : {μ ρ : Modality m n} (α : TwoCell μ ρ) {Γ : Ctx n} →
                  DRA.key-subst ⟦ α ⟧two-cell M.≅ˢ ⟦ keyʳ {Γ = Γ} (lock⟨ ρ ⟩, ◇) (lock⟨ μ ⟩, ◇) α ⟧ren
  ren-key-sound-cod : {μ : Modality m n} (Λ : LockTele n m) (α : TwoCell μ (locksˡᵗ Λ)) {Γ : Ctx n} →
                      DRA.key-subst ⟦ α ⟧two-cell M.⊚ M.from (,ˡᵗ-sound {Γ = Γ} Λ) M.≅ˢ ⟦ keyʳ Λ (lock⟨ μ ⟩, ◇) α ⟧ren
  ren-lock-sound : (σ : Ren Γ Δ) (μ : Modality m n) → ⟦ σ ,lockʳ⟨ μ ⟩ ⟧ren M.≅ˢ lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧ren
  ren-π-sound : (Γ : Ctx m) (x : String) (μ : Modality n m) (T : Ty n) → ⟦ πʳ {Γ = Γ} {μ = μ} {x} {T} ⟧ren M.≅ˢ M.π

  sub-key-sound : {μ ρ : Modality m n} (α : TwoCell μ ρ) {Γ : Ctx n} →
                  DRA.key-subst ⟦ α ⟧two-cell M.≅ˢ ⟦ keyˢ {Γ = Γ} (lock⟨ ρ ⟩, ◇) (lock⟨ μ ⟩, ◇) α ⟧sub
  sub-lock-sound : (σ : Sub Γ Δ) (μ : Modality m n) → ⟦ σ ,lockˢ⟨ μ ⟩ ⟧sub M.≅ˢ lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧sub
  sub-π-sound : (Γ : Ctx m) (x : String) (μ : Modality n m) (T : Ty n) → ⟦ πˢ {Γ = Γ} {μ = μ} {x} {T} ⟧sub M.≅ˢ M.π
  /cl-sound : {Γ : Ctx m} {μ : Modality n m} {T : Ty n} (t : Tm (Γ ,lock⟨ μ ⟩) T) (x : String) →
              ⟦ t / x ⟧sub M.≅ˢ (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm) M./cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩
  ∷ˢ-sound : (σ : Sub Γ Δ) {μ : Modality m n} (t : Tm (Γ ,lock⟨ μ ⟩) T) (x : String) →
             ⟦ σ ∷ˢ t / x ⟧sub M.≅ˢ ⟦ σ ⟧sub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm

atomic-rename-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (σ : AtomicRen Δ Γ) →
                         ⟦ t [ σ ]tmᵃʳ ⟧tm M.≅ᵗᵐ (⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl )
atomic-rename-tm-sound  σ = {!!}

postulate
  rename-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (σ : Ren Δ Γ) →
                    ⟦ t [ σ ]tmʳ ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧ren ]cl
  rename-bprop-sound : {Γ : Ctx m} (φ : bProp Γ) (σ : Ren Δ Γ) →
                       ⟦ φ [ σ ]bpropʳ ⟧bprop M.≅ᵗʸ ⟦ φ ⟧bprop M.[ ⟦ σ ⟧ren ]
  -- rename-tm-sound  {μ} {m} {Γ} {T} t Syn.RenSub.id =
  --   M.symᵗᵐ (M.cl-tm-subst-id (ty-closed-natural T) ⟦ t ⟧tm)
  -- rename-tm-sound t (id-ren ⊚a σ) = {!!}
  -- rename-tm-sound {Γ = Γ} {T = T} t (σs@(_ ⊚a _) ⊚a σ) = M.transᵗᵐ step3 (M.transᵗᵐ step1 step2)
  --   where step0 : ⟦ rename-tm t σs ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren ]cl
  --         step0 = rename-tm-sound t σs
  --         step1 : ⟦ rename-tm t σs ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl M.≅ᵗᵐ
  --                 ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren ]cl M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl
  --         step1 = M.cl-tm-subst-cong-tm (ty-closed-natural T) step0
  --         step2 : ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren ]cl M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl  M.≅ᵗᵐ
  --                 ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σs ⟧ren M.⊚ ⟦ σ ⟧aren ]cl
  --         step2 = M.cl-tm-subst-⊚ (ty-closed-natural T) ⟦ t ⟧tm
  --         step3 : ⟦ AtomicRen.atomic-rename-tm (rename-tm t σs) σ ⟧tm M.≅ᵗᵐ
  --                   ⟦ rename-tm t σs ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl
  --         step3 = atomic-rename-tm-sound (rename-tm t σs) σ

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
  M.transˢ (M.,cl-cong-cl (𝟙-preserves-cl (ty-closed-natural T))) (
  M.symˢ (M./v-/cl (ty-closed-natural T) ⟦ t ⟧tm))))

weaken-tm-sound : (Γ : Ctx m) (x : String) (μ : Modality n m) (S : Ty n) {T : Ty m} (t : Tm Γ T) →
                  ⟦ weaken-tm {μ = μ} {x} {S} t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.π ]cl
weaken-tm-sound Γ x μ S {T} t = M.transᵗᵐ (rename-tm-sound t πʳ) (M.cl-tm-subst-cong-subst (ty-closed-natural T) (ren-π-sound Γ x μ S))

v0-sound-𝟙 : (Γ : Ctx m) (x : String) (T : Ty m) →
             ⟦ v0 {Γ = Γ} {μ = 𝟙} {x = x} {T = T} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T)
v0-sound-𝟙 Γ x T = M.transᵗᵐ (v0-sound Γ 𝟙 x T) (M.ξcl-cong-cl (𝟙-preserves-cl (ty-closed-natural T)))

v1-sound-𝟙 : (Γ : Ctx m) (x : String) (T : Ty m) (κ : Modality n m) (y : String) (S : Ty n) →
             ⟦ v1 {Γ = Γ} {μ = 𝟙} {x} {T} {κ = κ} {y} {S} ⟧tm M.≅ᵗᵐ M.ξcl (ty-closed-natural T) M.[ ty-closed-natural T ∣ M.π ]cl
v1-sound-𝟙 Γ x T κ y S =
  M.transᵗᵐ (v1-sound Γ 𝟙 x T κ y S) (
  M.transᵗᵐ (M.cl-tm-subst-cong-cl (𝟙-preserves-cl (ty-closed-natural T))) (
  M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.ξcl-cong-cl (𝟙-preserves-cl (ty-closed-natural T)))))

,ˡᵗ-sound-to-naturalʳ : (Λ : LockTele m n) {Γ Δ : Ctx m} (σ : Ren Γ Δ) →
                        ⟦ σ ,locksʳ⟨ Λ ⟩ ⟧ren M.⊚ M.to (,ˡᵗ-sound Λ)
                          M.≅ˢ
                        M.to (,ˡᵗ-sound Λ) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧ren
,ˡᵗ-sound-to-naturalʳ ◇ σ = M.transˢ (M.id-subst-unitʳ _) (M.symˢ (M.id-subst-unitˡ _))
,ˡᵗ-sound-to-naturalʳ (lock⟨ μ ⟩, Λ) σ =
  begin
    ⟦ σ ,lockʳ⟨ μ ⟩ ,locksʳ⟨ Λ ⟩ ⟧ren M.⊚ (M.to (,ˡᵗ-sound Λ) M.⊚ key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
  ≅⟨ M.⊚-assoc ⟨
    (⟦ σ ,lockʳ⟨ μ ⟩ ,locksʳ⟨ Λ ⟩ ⟧ren M.⊚ M.to (,ˡᵗ-sound Λ)) M.⊚ key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))
  ≅⟨ M.⊚-congˡ (,ˡᵗ-sound-to-naturalʳ Λ (σ ,lockʳ⟨ μ ⟩)) ⟩
    (M.to (,ˡᵗ-sound Λ) M.⊚ lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ,lockʳ⟨ μ ⟩ ⟧ren) M.⊚ key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))
  ≅⟨ M.⊚-assoc ⟩
    M.to (,ˡᵗ-sound Λ) M.⊚ (lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ,lockʳ⟨ μ ⟩ ⟧ren M.⊚ key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
  ≅⟨ M.⊚-congʳ (M.⊚-congˡ (lock-fmap-cong ⟦ locksˡᵗ Λ ⟧mod (ren-lock-sound σ μ))) ⟩
    M.to (,ˡᵗ-sound Λ) M.⊚ (lock-fmap ⟦ locksˡᵗ Λ ⟧mod (lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧ren) M.⊚ key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
  ≅⟨ M.⊚-congʳ (key-subst-natural (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))) ⟨
    M.to (,ˡᵗ-sound Λ) M.⊚ (key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧ren)
  ≅⟨ M.⊚-assoc ⟨
    M.to (,ˡᵗ-sound Λ) M.⊚ key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧ren ∎
  where open M.≅ˢ-Reasoning
