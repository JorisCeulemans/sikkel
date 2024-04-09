open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT.RenSubSoundness
  (𝒫 : MSTT-Parameter)
  where

open import Data.List
open import Data.String using (String)
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Model.Type.Constant as M
import Model.Type.Function as M
import Model.Type.Product as M

open MSTT-Parameter 𝒫
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯
open TmExtSem ⟦𝓉⟧
open import Experimental.LogicalFramework.MSTT 𝒫

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n
  x y : String


record TravStructSemantics
  {Trav : ∀ {m} → Ctx m → Ctx m → Set}
  (trav-struct : TravStruct Trav)
  : Set where

  no-eta-equality

  module TS = TravStruct trav-struct
  open TS

  field
    ⟦_⟧trav : Trav Γ Δ → (⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx)
    vr-sound : {Γ Δ : Ctx m} {T : Ty m} →
               (v : Var x T Δ ◇) (σ : Trav Γ Δ) →
               ⟦ v ⟧var M.[ ty-closed-natural T ∣ ⟦ σ ⟧trav ]cl M.≅ᵗᵐ ⟦ vr v σ ⟧tm
    lift-sound : {Γ Δ : Ctx m} {μ : Modality n m} {x : String} {T : Ty n} (σ : Trav Γ Δ) →
                 M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧trav M.≅ˢ ⟦ lift {μ = μ} {x = x} {T = T} σ ⟧trav
    lock-sound : {Γ Δ : Ctx m} (σ : Trav Γ Δ) (μ : Modality n m) →
                 lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧trav M.≅ˢ ⟦ TS.lock {μ = μ} σ ⟧trav

  lift-trav-tel-sound : (σ : Trav Γ Δ) (Θ : Telescope m n) →
                        lift-sem-tel Θ ⟦ σ ⟧trav M.≅ˢ ⟦ lift-trav-tel σ Θ ⟧trav
  lift-trav-tel-sound σ ◇ = M.reflˢ
  lift-trav-tel-sound σ (Θ ,, μ ∣ x ∈ T) =
    M.transˢ (M.lift-cl-subst-cong (ty-closed-natural ⟨ μ ∣ T ⟩) (lift-trav-tel-sound σ Θ)) (lift-sound {μ = μ} {T = T} (lift-trav-tel σ Θ))
  lift-trav-tel-sound σ (Θ ,lock⟨ μ ⟩) =
    M.transˢ (DRA.lock-fmap-cong ⟦ μ ⟧mod (lift-trav-tel-sound σ Θ)) (lock-sound (lift-trav-tel σ Θ) μ)


  traverse-tm-sound : (t : Tm Δ T) (σ : Trav Γ Δ) →
                      ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧trav ]cl M.≅ᵗᵐ ⟦ traverse-tm t σ ⟧tm
  traverse-ext-tmargs-sound : ∀ {arginfos} (args : ExtTmArgs arginfos Δ) (σ : Trav Γ Δ) →
                              semtms-subst ⟦ args ⟧extargs ⟦ σ ⟧trav
                                ≅ᵗᵐˢ
                              ⟦ traverse-ext-tmargs args σ ⟧extargs

  traverse-tm-sound (var' x {v}) σ = vr-sound v σ
  traverse-tm-sound (mod⟨_⟩_ {T = T} μ t) σ =
    M.transᵗᵐ (dra-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t ⟧tm) (
    M.transᵗᵐ (dra-intro-cong ⟦ μ ⟧mod (M.cl-tm-subst-cong-subst (ty-closed-natural T) (lock-sound σ μ))) (
    dra-intro-cong ⟦ μ ⟧mod (traverse-tm-sound t (TS.lock σ))))
  traverse-tm-sound (mod-elim {T = T} {S = S} ρ μ x t s) σ =
    M.transᵗᵐ (dra-let-natural ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T) (ty-closed-natural S) ⟦ σ ⟧trav) (
    dra-let-cong ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T) (ty-closed-natural S)
                 (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural ⟨ μ ∣ T ⟩) (lock-sound σ ρ))
                            (traverse-tm-sound t (TS.lock σ)))
                 (M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural S)
                                                          (M.transˢ (M.⊚-congʳ (M.symˢ (M.lift-cl-subst-cong-cl (ⓓ-preserves-cl ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T)))))
                                                                    (M.lift-cl-,,-cong-commute (M.symᶜᵗʸ (eq-dra-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))) ⟦ σ ⟧trav)))
                            (M.cl-tm-subst-cong-tm (ty-closed-natural S)
                                                   (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural S) (lift-sound σ))
                                                              (traverse-tm-sound s (TS.lift σ))))))
  traverse-tm-sound (lam[_∣_∈_]_ {S = S} μ x T s) σ =
    M.transᵗᵐ (M.lamcl-natural (ty-closed-natural ⟨ μ ∣ T ⟩) (ty-closed-natural S)) (
    M.transᵗᵐ (M.lamcl-cong (ty-closed-natural S) (M.cl-tm-subst-cong-subst (ty-closed-natural S) (lift-sound σ))) (
    M.lamcl-cong (ty-closed-natural S) (traverse-tm-sound s (TS.lift σ))))
  traverse-tm-sound (_∙_ {T = T} {S = S} {μ = μ} f t) σ =
    M.transᵗᵐ (M.app-cl-natural (ty-closed-natural ⟨ μ ∣ T ⟩) (ty-closed-natural S)) (
    M.transᵗᵐ (M.app-cong M.reflᵗᵐ (dra-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t ⟧tm)) (
    M.app-cong (traverse-tm-sound f σ)
               (dra-intro-cong ⟦ μ ⟧mod (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (lock-sound σ μ))
                                                   (traverse-tm-sound t (TS.lock σ))))))
  traverse-tm-sound zero σ = M.const-cl-natural ⟦ σ ⟧trav
  traverse-tm-sound (suc t) σ = M.transᵗᵐ (M.suc'-cl-natural ⟦ σ ⟧trav) (M.suc'-cong (traverse-tm-sound t σ))
  traverse-tm-sound (nat-rec {A = A} z s n) σ =
    M.transᵗᵐ (M.nat-rec-cl-natural (ty-closed-natural A)) (
    M.nat-rec-cong (traverse-tm-sound z σ)
                   (M.transᵗᵐ (M.symᵗᵐ (M.cl-tm-subst-cong-cl (⇛-closed-natural A A))) (traverse-tm-sound s σ))
                   (traverse-tm-sound n σ))
  traverse-tm-sound true σ = M.const-cl-natural ⟦ σ ⟧trav
  traverse-tm-sound false σ = M.const-cl-natural ⟦ σ ⟧trav
  traverse-tm-sound (if {A = A} b t f) σ =
    M.transᵗᵐ (M.if'-cl-natural (ty-closed-natural A)) (M.if'-cong (traverse-tm-sound b σ) (traverse-tm-sound t σ) (traverse-tm-sound f σ))
  traverse-tm-sound (pair {T = T} {S = S} t s) σ =
    M.transᵗᵐ (M.pair-cl-natural (ty-closed-natural T) (ty-closed-natural S)) (M.pair-cong (traverse-tm-sound t σ) (traverse-tm-sound s σ))
  traverse-tm-sound (fst {T = T} {S = S} p) σ = M.transᵗᵐ (M.fst-cl-natural (ty-closed-natural T) (ty-closed-natural S)) (M.fst-cong (traverse-tm-sound p σ))
  traverse-tm-sound (snd {T = T} {S = S} p) σ = M.transᵗᵐ (M.snd-cl-natural (ty-closed-natural T) (ty-closed-natural S)) (M.snd-cong (traverse-tm-sound p σ))
  traverse-tm-sound {Γ = Γ} (Tm.ext c tm-args refl) σ =
    M.transᵗᵐ (apply-sem-tm-constructor-natural {Γ = Γ} ⟦ c ⟧tm-code (⟦⟧tm-code-natural c) ⟦ σ ⟧trav _)
              (apply-sem-tm-constructor-cong {Γ = Γ} ⟦ c ⟧tm-code (⟦⟧tm-code-cong c) (traverse-ext-tmargs-sound tm-args σ))

  traverse-ext-tmargs-sound {arginfos = []}          _            σ = tt
  traverse-ext-tmargs-sound {arginfos = arginfo ∷ _} (arg , args) σ =
    M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural (tmarg-ty arginfo)) (lift-trav-tel-sound σ (tmarg-tel arginfo)))
              (traverse-tm-sound arg (lift-trav-tel σ (tmarg-tel arginfo)))
    , traverse-ext-tmargs-sound args σ


{-
postulate
  tm-sub-sound : (t : Tm Δ T) (σ : Sub Γ Δ) → ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧sub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tmˢ ⟧tm

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

postulate
  rename-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (σ : Ren Δ Γ) →
                    ⟦ t [ σ ]tmʳ ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧ren ]cl
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
  {!!}

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
-}
