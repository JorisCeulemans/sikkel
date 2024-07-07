open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension using (TyExt)
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics using (TmExtSem)

module Experimental.LogicalFramework.MSTT.Soundness.Substitution
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.List
open import Data.Product
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Ag

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding
  (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; lock-fmap; lock-fmap-cong; lock-fmap-id; lock-fmap-⊚
  ; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_; key-subst; key-subst-natural; key-subst-eq)
import Model.Type.Constant as M
import Model.Type.Function as M
import Model.Type.Product as M

open ModeTheory ℳ
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 hiding (TmExt)
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯 hiding (TmExtSem)
open TmExtSem ⟦𝓉⟧
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ 𝒯 𝓉 ⟦𝓉⟧
open import Experimental.LogicalFramework.MSTT.Soundness.LockTele ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Soundness.Variable ℳ 𝒯 𝓉 ⟦𝓉⟧

private variable
  m n o : Mode
  Γ Δ : Ctx m
  T S : Ty m
  μ ρ : Modality m n
  x y : Name


record TravStructSoundness
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
    lift-sound : {Γ Δ : Ctx m} {μ : Modality n m} {x : Name} {T : Ty n} (σ : Trav Γ Δ) →
                 M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧trav M.≅ˢ ⟦ lift {μ = μ} {x = x} {T = T} σ ⟧trav
    lock-sound : {Γ Δ : Ctx m} (σ : Trav Γ Δ) (μ : Modality n m) →
                 DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧trav M.≅ˢ ⟦ TS.lock {μ = μ} σ ⟧trav

  lift-trav-tel-sound : (σ : Trav Γ Δ) (Θ : NamelessTele m n) {names : Names Θ} →
                        M.to (++tel-++⟦⟧nltel Δ Θ names) M.⊚ apply-nltel-sub ⟦ σ ⟧trav Θ
                          M.≅ˢ
                        ⟦ lift-trav-tel σ (add-names Θ names) ⟧trav M.⊚ M.to (++tel-++⟦⟧nltel Γ Θ names)
  lift-trav-tel-sound σ ◇ = M.transˢ (M.id-subst-unitˡ _) (M.symˢ (M.id-subst-unitʳ _))
  lift-trav-tel-sound σ (Θ ,, μ ∣ T) =
    M.transˢ (M.ctx-fmap-cong-2-2 (M.,,-functor (ty-closed-natural ⟨ μ ∣ T ⟩)) (lift-trav-tel-sound σ Θ))
             (M.⊚-congˡ (lift-sound {μ = μ} {T = T} (lift-trav-tel σ _)))
  lift-trav-tel-sound σ (Θ ,lock⟨ μ ⟩) =
    M.transˢ (M.ctx-fmap-cong-2-2 (DRA.ctx-functor ⟦ μ ⟧mod) (lift-trav-tel-sound σ Θ))
             (M.⊚-congˡ (lock-sound (lift-trav-tel σ _) μ))


  traverse-tm-sound : (t : Tm Δ T) (σ : Trav Γ Δ) →
                      ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧trav ]cl M.≅ᵗᵐ ⟦ traverse-tm t σ ⟧tm
  traverse-ext-tmargs-sound : ∀ {arginfos} {names : TmArgBoundNames arginfos}
                              (args : ExtTmArgs arginfos names Δ) (σ : Trav Γ Δ) →
                              semtms-subst ⟦ args ⟧tmextargs ⟦ σ ⟧trav
                                ≅ᵗᵐˢ
                              ⟦ traverse-ext-tmargs args σ ⟧tmextargs

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
  traverse-tm-sound {Γ = Γ} (Tm.ext c names tm-args refl) σ =
    M.transᵗᵐ (apply-sem-tm-constructor-natural {Γ = Γ} ⟦ c ⟧tm-code (⟦⟧tm-code-natural c) ⟦ σ ⟧trav _)
              (apply-sem-tm-constructor-cong {Γ = Γ} ⟦ c ⟧tm-code (⟦⟧tm-code-cong c) (traverse-ext-tmargs-sound tm-args σ))
  traverse-tm-sound (global-def {T = T} _ {t}) σ = M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (M.◇-terminal _ _ _)

  traverse-ext-tmargs-sound {arginfos = []}          _            σ = tt
  traverse-ext-tmargs-sound {arginfos = arginfo ∷ _} (arg , args) σ =
    M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural (tmarg-ty arginfo)) (lift-trav-tel-sound σ (tmarg-tel arginfo)))
              (M.cl-tm-subst-cong-tm (ty-closed-natural (tmarg-ty arginfo)) (traverse-tm-sound arg (lift-trav-tel σ _)))
    , traverse-ext-tmargs-sound args σ

open TravStructSoundness using (traverse-tm-sound)


record RenSubDataStructureSound
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  (⟦_⟧rensubdata : RenSubDataSemantics V)
  : Set where

  open RenSubDataStructure rensub-struct
  open AtomicRenSubDef V
  open RenSubSemantics V ⟦_⟧rensubdata

  field
    newV-sound : ∀ {x m n} {μ : Modality n m} {T : Ty n} {Γ : Ctx m} →
                 dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)) M.≅ᵗᵐ ⟦ newV {x} {μ = μ} {T = T} {Γ = Γ} ⟧rensubdata
    atomic-rensub-lookup-var-sound :
      ∀ {x m} {Γ Δ : Ctx m} {T : Ty m} (v : Var x T Δ ◇) (σ : AtomicRenSub Γ Δ) →
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ ⟦ σ ⟧arensub ]cl M.≅ᵗᵐ ⟦ atomic-rensub-lookup-var v σ ⟧tm


module AtomicRenSubSoundness
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  (⟦_⟧rensubdata : RenSubDataSemantics V)
  (rensub-struct-sound : RenSubDataStructureSound V rensub-struct ⟦_⟧rensubdata)
  where

  open AtomicRenSub V rensub-struct
  open RenSubSemantics V ⟦_⟧rensubdata
  open RenSubDataStructureSound rensub-struct-sound

  πᵃ-sound : ∀ {m n} (Γ : Ctx n) (μ : Modality m n) (x : Name) (T : Ty m) →
             M.π M.≅ˢ ⟦ πᵃ {Γ = Γ} {μ = μ} {x = x} {T = T} ⟧arensub
  πᵃ-sound _ _ _ _ = M.symˢ (M.id-subst-unitˡ _)

  liftᵃ-sound : ∀ {m n x} {Γ Δ : Ctx n} {μ : Modality m n} {T : Ty m} (σ : AtomicRenSub Γ Δ) →
                M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧arensub
                  M.≅ˢ
                ⟦ liftᵃ {μ = μ} {x = x} {T = T} σ ⟧arensub
  liftᵃ-sound {μ = μ} {T} σ =
    M.,cl-cong-tm (ty-closed-natural ⟨ μ ∣ T ⟩) (M.transᵗᵐ (M.symᵗᵐ (dra-η ⟦ μ ⟧mod _)) (dra-intro-cong ⟦ μ ⟧mod newV-sound))

  locksᵃ-sound : ∀ {m n} {Γ Δ : Ctx m} (σ : AtomicRenSub Γ Δ) (Λ : LockTele m n) →
                 M.to (,ˡᵗ-sound Λ)
                 M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧arensub
                 M.⊚ M.from (,ˡᵗ-sound Λ)
                   M.≅ˢ
                 ⟦ σ ,locksᵃ⟨ Λ ⟩ ⟧arensub
  locksᵃ-sound σ ◇ = M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _)
  locksᵃ-sound σ (lock⟨ μ ⟩, Λ) =
    begin
      (M.to (,ˡᵗ-sound Λ) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
      M.⊚ DRA.lock-fmap ⟦ μ ⓜ locksˡᵗ Λ ⟧mod ⟦ σ ⟧arensub
      M.⊚ (DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ M.from (,ˡᵗ-sound Λ))
    ≅⟨ M.⊚-congˡ (M.transˢ M.⊚-assoc (M.⊚-congʳ (DRA.key-subst-natural (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))))) ⟩
      M.to (,ˡᵗ-sound Λ)
      M.⊚ (DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧arensub) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
      M.⊚ (DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ M.from (,ˡᵗ-sound Λ))
    ≅⟨ M.transˢ (M.symˢ M.⊚-assoc) (M.⊚-congˡ (M.transˢ (M.⊚-congˡ (M.symˢ M.⊚-assoc)) (M.transˢ M.⊚-assoc (
                M.transˢ (M.⊚-congʳ (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))) (M.id-subst-unitʳ _))))) ⟩
      M.to (,ˡᵗ-sound Λ)
      M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧arensub)
      M.⊚ M.from (,ˡᵗ-sound Λ)
    ≅⟨ locksᵃ-sound (σ ,lockᵃ⟨ μ ⟩) Λ ⟩
      ⟦ (σ ,lockᵃ⟨ μ ⟩) ,locksᵃ⟨ Λ ⟩ ⟧arensub ∎
    where open M.≅ˢ-Reasoning

  AtomicRenSubTravSound : TravStructSoundness AtomicRenSubTrav
  TravStructSoundness.⟦_⟧trav AtomicRenSubTravSound = ⟦_⟧arensub
  TravStructSoundness.vr-sound AtomicRenSubTravSound = atomic-rensub-lookup-var-sound
  TravStructSoundness.lift-sound AtomicRenSubTravSound {μ = μ} σ = liftᵃ-sound {μ = μ} σ
  TravStructSoundness.lock-sound AtomicRenSubTravSound σ μ = M.reflˢ

  tm-arensub-sound : (t : Tm Δ T) (σ : AtomicRenSub Γ Δ) →
                     ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧arensub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tmᵃ ⟧tm
  tm-arensub-sound t σ = traverse-tm-sound AtomicRenSubTravSound t σ


module RenSubSoundness
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  (⟦_⟧rensubdata : RenSubDataSemantics V)
  (rensub-struct-sound : RenSubDataStructureSound V rensub-struct ⟦_⟧rensubdata)
  where

  open RenSub V rensub-struct
  open RenSubSemantics V ⟦_⟧rensubdata
  open RenSubDataStructureSound rensub-struct-sound
  open AtomicRenSub V rensub-struct
  open AtomicRenSubSoundness V rensub-struct ⟦_⟧rensubdata rensub-struct-sound

  tm-rensub-sound : (t : Tm Δ T) (σ : RenSub Γ Δ) →
                    ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧rensub ]cl M.≅ᵗᵐ ⟦ t [ σ ]tmʳˢ ⟧tm
  tm-rensub-sound {T = T} t id = M.cl-tm-subst-id (ty-closed-natural T) ⟦ t ⟧tm
  tm-rensub-sound t (id ⊚a τᵃ) = tm-arensub-sound t τᵃ
  tm-rensub-sound {T = T} t (σ@(_ ⊚a _) ⊚a τᵃ) =
    begin
      ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub ]cl
    ≅⟨ M.cl-tm-subst-⊚ (ty-closed-natural T) ⟦ t ⟧tm ⟨
      ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ σ ⟧rensub ]cl M.[ ty-closed-natural T ∣ ⟦ τᵃ ⟧arensub ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (tm-rensub-sound t σ) ⟩
      ⟦ t [ σ ]tmʳˢ ⟧tm M.[ ty-closed-natural T ∣ ⟦ τᵃ ⟧arensub ]cl
    ≅⟨ tm-arensub-sound (t [ σ ]tmʳˢ) τᵃ ⟩
      ⟦ t [ σ ]tmʳˢ [ τᵃ ]tmᵃ ⟧tm ∎
    where open M.≅ᵗᵐ-Reasoning

  liftʳˢ-sound : ∀ {m n x} {Γ Δ : Ctx n} {μ : Modality m n} {T : Ty m} (σ : RenSub Γ Δ) →
                 M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧rensub
                   M.≅ˢ
                 ⟦ liftʳˢ {μ = μ} {x = x} {T = T} σ ⟧rensub
  liftʳˢ-sound {μ = μ} {T = T} id = M.lift-cl-subst-id (ty-closed-natural ⟨ μ ∣ T ⟩)
  liftʳˢ-sound {μ = μ} (id ⊚a τᵃ) = liftᵃ-sound {μ = μ} τᵃ
  liftʳˢ-sound {x = x} {μ = μ} {T = T} (σ@(_ ⊚a _) ⊚a τᵃ) =
    begin
      M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) (⟦ σ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub)
    ≅⟨ M.lift-cl-subst-⊚ (ty-closed-natural ⟨ μ ∣ T ⟩) ⟩
      M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧rensub M.⊚ M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ τᵃ ⟧arensub
    ≅⟨ M.⊚-congˡ (liftʳˢ-sound {x = x} {μ = μ} {T = T} σ) ⟩
      ⟦ liftʳˢ σ ⟧rensub M.⊚ M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ τᵃ ⟧arensub
    ≅⟨ M.⊚-congʳ (liftᵃ-sound {μ = μ} τᵃ) ⟩
      ⟦ liftʳˢ σ ⟧rensub M.⊚ ⟦ liftᵃ {μ = μ} {T = T} τᵃ ⟧arensub ∎
    where open M.≅ˢ-Reasoning

  []ʳˢ-sound : {Γ : Ctx m} → M.!◇ _ M.≅ˢ ⟦ []ʳˢ {Γ = Γ} ⟧rensub
  []ʳˢ-sound = M.reflˢ

  πʳˢ-sound : ∀ {m n} (Γ : Ctx n) (μ : Modality m n) (x : Name) (T : Ty m) →
              M.π M.≅ˢ ⟦ πʳˢ {Γ = Γ} {μ = μ} {x = x} {T = T} ⟧rensub
  πʳˢ-sound Γ μ x T = πᵃ-sound Γ μ x T

  ∷ʳˢ-sound : (σ : RenSub Γ Δ) (v : V μ T Γ) (x : Name) →
              ⟦ σ ⟧rensub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ v ⟧rensubdata
                M.≅ˢ
              ⟦ σ ∷ʳˢ v / x ⟧rensub
  ∷ʳˢ-sound id v x = M.reflˢ
  ∷ʳˢ-sound (id ⊚a τᵃ) v x = M.reflˢ
  ∷ʳˢ-sound {μ = μ} {T = T} (σ@(_ ⊚a _) ⊚a τᵃ) v x =
    begin
      (⟦ σ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub) M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ v ⟧rensubdata
    ≅⟨ M.lift-cl-,cl (ty-closed-natural ⟨ μ ∣ T ⟩) ⟨
      (M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧rensub) M.⊚ (⟦ τᵃ ⟧arensub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ v ⟧rensubdata)
    ≅⟨ M.⊚-congˡ (liftʳˢ-sound σ) ⟩
      ⟦ liftʳˢ σ ⟧rensub M.⊚ (⟦ τᵃ ⟧arensub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ v ⟧rensubdata)  ∎
    where open M.≅ˢ-Reasoning

  lockʳˢ-sound : {Γ Δ : Ctx n} (σ : RenSub Γ Δ) (μ : Modality m n) →
                 DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧rensub M.≅ˢ ⟦ σ ,lockʳˢ⟨ μ ⟩ ⟧rensub
  lockʳˢ-sound id μ = DRA.lock-fmap-id ⟦ μ ⟧mod
  lockʳˢ-sound (id ⊚a τᵃ) μ = M.reflˢ
  lockʳˢ-sound (σ@(_ ⊚a _) ⊚a τᵃ) μ =
    begin
      DRA.lock-fmap ⟦ μ ⟧mod (⟦ σ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub)
    ≅⟨ DRA.lock-fmap-⊚ ⟦ μ ⟧mod _ _ ⟩
      DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧rensub M.⊚ DRA.lock-fmap ⟦ μ ⟧mod ⟦ τᵃ ⟧arensub
    ≅⟨ M.⊚-congˡ (lockʳˢ-sound σ μ) ⟩
      ⟦ σ ,lockʳˢ⟨ μ ⟩ ⟧rensub M.⊚ DRA.lock-fmap ⟦ μ ⟧mod ⟦ τᵃ ⟧arensub ∎
    where open M.≅ˢ-Reasoning

  ⊚ʳˢ-sound : {Γ Δ Θ : Ctx m} (σ : RenSub Δ Θ) (τ : RenSub Γ Δ) →
              ⟦ σ ⟧rensub M.⊚ ⟦ τ ⟧rensub M.≅ˢ ⟦ σ ⊚ʳˢ τ ⟧rensub
  ⊚ʳˢ-sound σ id = M.id-subst-unitʳ _
  ⊚ʳˢ-sound id (id ⊚a τᵃ) = M.id-subst-unitˡ _
  ⊚ʳˢ-sound (σ ⊚a σᵃ) (id ⊚a τᵃ) = M.reflˢ
  ⊚ʳˢ-sound σ (τ@(_ ⊚a _) ⊚a τᵃ) =
    begin
      ⟦ σ ⟧rensub M.⊚ (⟦ τ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub)
    ≅⟨ M.⊚-assoc ⟨
      (⟦ σ ⟧rensub M.⊚ ⟦ τ ⟧rensub) M.⊚ ⟦ τᵃ ⟧arensub
    ≅⟨ M.⊚-congˡ (⊚ʳˢ-sound σ τ) ⟩
      ⟦ σ ⊚ʳˢ τ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub ∎
    where open M.≅ˢ-Reasoning


module TwoCellSoundness where
  open M.≅ᵗᵐ-Reasoning

  apply-2-cell-var-sound : (Θ Ψ : LockTele n m) (α : TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ)) (v : Var x T Γ Θ) →
                           ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl M.≅ᵗᵐ ⟦ apply-2-cell-var Θ Ψ α v ⟧var
  apply-2-cell-var-sound {T = T} Θ Ψ α (vzero {μ = μ} β) =
    begin
      dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ β ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (M.symˢ (DRA.key-subst-eq (⟦ⓣ-vert⟧-sound α β))) ⟩
      dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⓣ-vert β ⟧two-cell ]cl ∎
  apply-2-cell-var-sound {T = T} Θ Ψ α (vsuc v) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Θ ⟧mod M.π ]cl M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (DRA.key-subst-natural ⟦ α ⟧two-cell) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Ψ ⟧mod M.π ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (apply-2-cell-var-sound Θ Ψ α v) ⟩
      ⟦ apply-2-cell-var Θ Ψ α v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Ψ ⟧mod M.π ]cl ∎
  apply-2-cell-var-sound {T = T} Θ Ψ α (vlock {ρ = ρ} v) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Θ))) ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M.transˢ (M.⊚-congˡ (DRA.lock-fmap-id ⟦ locksˡᵗ Θ ⟧mod)) (M.id-subst-unitˡ _)) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Θ))) ]cl
               M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Θ ⟧mod (M.id-subst _) M.⊚ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.ⓣ-hor-key-subst (DRA.id-cell {μ = ⟦ ρ ⟧mod}) ⟦ α ⟧two-cell) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Θ))) ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst (DRA.id-cell {μ = ⟦ ρ ⟧mod} DRA.ⓣ-hor ⟦ α ⟧two-cell) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.key-subst-eq (DRA.ⓣ-hor-congˡ {α = ⟦ α ⟧two-cell} ⟦id-cell⟧-sound)) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Θ))) ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst (⟦ id-cell {μ = ρ} ⟧two-cell DRA.ⓣ-hor ⟦ α ⟧two-cell) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (DRA.key-subst-eq (⟦ⓜ⟧-sound-natural id-cell α)) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell ⓣ-hor α ⟧two-cell ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Ψ))) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (apply-2-cell-var-sound (lock⟨ ρ ⟩, Θ) (lock⟨ ρ ⟩, Ψ) (id-cell ⓣ-hor α) v) ⟩
      ⟦ apply-2-cell-var (lock⟨ ρ ⟩, Θ) (lock⟨ ρ ⟩, Ψ) (id-cell ⓣ-hor α) v ⟧var
        M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Ψ))) ]cl ∎

  apply-2-cell-var-lt-sound : (Θ Ψ : LockTele n m) (α : TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ))
                              {Λ : LockTele m o} (v : Var x T (Γ ,ˡᵗ Θ) Λ) →
                              ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (
                                             M.to (,ˡᵗ-sound Θ)
                                             M.⊚ DRA.key-subst ⟦ α ⟧two-cell
                                             M.⊚ M.from (,ˡᵗ-sound Ψ))
                                         ]cl
                                M.≅ᵗᵐ
                              ⟦ apply-2-cell-var-lt Θ Ψ α v ⟧var
  apply-2-cell-var-lt-sound {T = T} Θ Ψ α {Λ} v =
    begin
      ⟦ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (
            M.to (,ˡᵗ-sound Θ)
            M.⊚ DRA.key-subst ⟦ α ⟧two-cell
            M.⊚ M.from (,ˡᵗ-sound Ψ))
          ]cl
    ≅⟨ M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _)) (M.symᵗᵐ (M.cl-tm-subst-⊚ (ty-closed-natural T) _)) ⟩
      ⟦ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (
            M.to (,ˡᵗ-sound Θ)
            M.⊚ DRA.key-subst ⟦ α ⟧two-cell)
          ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _))
                                                              (M.symᵗᵐ (M.cl-tm-subst-⊚ (ty-closed-natural T) _))) ⟩
      ⟦ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst ⟦ α ⟧two-cell) ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T)
                  (M.transˢ (M.transˢ (M.symˢ M.⊚-assoc) (M.⊚-congˡ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.transˢ (M.symˢ M.⊚-assoc)
                                      (M.transˢ (M.⊚-congˡ (DRA.key-subst-eq (⟦eq-cell-symˡ⟧ (++ˡᵗ-locks Θ)))) (M.id-subst-unitˡ _)))))))
                  (M.transˢ (M.⊚-congˡ (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))))) (M.id-subst-unitˡ _)))) ⟨
      ⟦ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                                  M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Θ {Λ}) ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell
                                  M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                                  M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst ⟦ α ⟧two-cell)
          ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T)
                  (M.transˢ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.transˢ (M.symˢ M.⊚-assoc) (M.transˢ (M.⊚-congˡ
                                      (DRA.key-subst-eq (⟦eq-cell-symˡ⟧ (++ˡᵗ-locks Ψ)))) (M.id-subst-unitˡ _)))))
                            (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))))) (M.id-subst-unitʳ _))))) ⟨
      ⟦ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                                  M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Θ) ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell
                                  M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                                  M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst ⟦ α ⟧two-cell)
                                  M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ)))
                                  M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Ψ {Λ}) ⟧two-cell
          ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Ψ)) ⟧two-cell
                                  M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))) ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst (ty-closed-natural T) (
       whiskerˡᵗ-right-sound-key Θ Ψ α))) ⟩
      ⟦ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                                  M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Θ {Λ}) ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ whiskerˡᵗ-right Θ Ψ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Ψ)) ⟧two-cell
                                  M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))) ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (unvlocks-sound Θ v))) ⟩
      ⟦ unvlocks Θ v ⟧var
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ whiskerˡᵗ-right Θ Ψ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Ψ)) ⟧two-cell
                                  M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))) ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (
         apply-2-cell-var-sound (Θ ++ˡᵗ Λ) (Ψ ++ˡᵗ Λ) (whiskerˡᵗ-right Θ Ψ α) (unvlocks Θ v))) ⟩
      ⟦ apply-2-cell-var (Θ ++ˡᵗ Λ) (Ψ ++ˡᵗ Λ) (whiskerˡᵗ-right Θ Ψ α) (unvlocks Θ v) ⟧var
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Ψ)) ⟧two-cell
                                  M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))) ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Ψ)) ]cl
    ≅⟨ vlocks-sound Ψ _ ⟩
      ⟦ vlocks Ψ (apply-2-cell-var (Θ ++ˡᵗ Λ) (Ψ ++ˡᵗ Λ) (whiskerˡᵗ-right Θ Ψ α) (unvlocks Θ v)) ⟧var ∎


module AtomicRenVarSound where
  open AtomicRenVar
  open SomeVar using (get-var)
  open TwoCellSoundness

  open M.≅ᵗᵐ-Reasoning

  atomic-ren-var'-sound : {Γ Δ : Ctx n} (Λ : LockTele n m) (v : Var x T Δ Λ) (σ : AtomicRen Γ Δ) →
                          ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧aren ]cl
                            M.≅ᵗᵐ
                          ⟦ get-var (atomic-ren-var' Λ v σ) ⟧var
  atomic-ren-var'-sound {T = T} Λ v idᵃʳ =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.id-subst _) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-id ⟦ locksˡᵗ Λ ⟧mod) ⟩
      (⟦ v ⟧var M.[ ty-closed-natural T ∣ M.id-subst _ ]cl)
    ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟩
      ⟦ v ⟧var ∎
  atomic-ren-var'-sound {T = T} Λ v (σ ⊚πᵃʳ) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (⟦ σ ⟧aren M.⊚ M.π) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _) ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ (DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧aren) M.⊚ (DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π) ]cl
    ≅⟨ M.cl-tm-subst-⊚ (ty-closed-natural T) _ ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧aren ]cl M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (atomic-ren-var'-sound Λ v σ) ⟩
      ⟦ get-var (atomic-ren-var' Λ v σ) ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl ∎
  atomic-ren-var'-sound {T = T} Λ (vlock v) (σ ,lockᵃʳ⟨ μ ⟩) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
               M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧aren) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (DRA.key-subst-natural (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))) ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧aren ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (atomic-ren-var'-sound (lock⟨ μ ⟩, Λ) v σ) ⟩
      ⟦ get-var (atomic-ren-var' (lock⟨ μ ⟩, Λ) v σ) ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl ∎
  atomic-ren-var'-sound {T = T} Λ v (keyᵃʳ Θ Ψ α) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Ψ) M.⊚ DRA.key-subst ⟦ α ⟧two-cell M.⊚ M.from (,ˡᵗ-sound Θ)) ]cl
    ≅⟨ apply-2-cell-var-lt-sound Ψ Θ α v ⟩
      ⟦ apply-2-cell-var-lt Ψ Θ α v ⟧var ∎
  atomic-ren-var'-sound {T = T} Λ (vzero {μ = μ} α) (σ ∷ᵃʳ somevar w / x) =
    begin
      dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (⟦ σ ⟧aren M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ w ⟧var) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (DRA.key-subst-natural ⟦ α ⟧two-cell) ⟩
      dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ μ ⟧mod (⟦ σ ⟧aren M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ w ⟧var) ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (dra-elim-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) _) ⟩
      dra-elim ⟦ μ ⟧mod (
               M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩) M.[ ty-closed-natural ⟨ μ ∣ T ⟩ ∣ ⟦ σ ⟧aren M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ w ⟧var ]cl)
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (dra-elim-cong ⟦ μ ⟧mod (M.,cl-β2 (ty-closed-natural ⟨ μ ∣ T ⟩) _ _)) ⟩
      dra-elim ⟦ μ ⟧mod (dra-intro ⟦ μ ⟧mod ⟦ w ⟧var)
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (dra-β ⟦ μ ⟧mod _) ⟩
      ⟦ w ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
    ≅⟨ apply-2-cell-var-sound (lock⟨ μ ⟩, ◇) Λ α w ⟩
      ⟦ apply-2-cell-var (lock⟨ μ ⟩, ◇) Λ α w ⟧var ∎
  atomic-ren-var'-sound {T = T} Λ (vsuc v) (_∷ᵃʳ_/_ {μ = ρ} {T = S} σ _ y) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl
               M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (⟦ σ ⟧aren M.,cl⟨ ty-closed-natural ⟨ ρ ∣ S ⟩ ⟩ _) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (M.transˢ (M.symˢ (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _))
                                                                    (DRA.lock-fmap-cong ⟦ locksˡᵗ Λ ⟧mod (M.,cl-β1 (ty-closed-natural ⟨ ρ ∣ S ⟩) ⟦ σ ⟧aren _))) ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧aren ]cl
    ≅⟨ atomic-ren-var'-sound Λ v σ ⟩
      ⟦ get-var (atomic-ren-var' Λ v σ) ⟧var ∎

  atomic-ren-var-sound : (v : Var x T Δ ◇) (σ : AtomicRen Γ Δ) →
                         ⟦ v ⟧var M.[ ty-closed-natural T ∣ ⟦ σ ⟧aren ]cl M.≅ᵗᵐ ⟦ atomic-ren-var v σ ⟧tm
  atomic-ren-var-sound v σ = atomic-ren-var'-sound ◇ v σ

  ren-data-struct-sound : RenSubDataStructureSound RenData ren-data-struct ren-data-semantics
  RenSubDataStructureSound.newV-sound ren-data-struct-sound {x = x} {μ = μ} {T = T} {Γ = Γ} = vzero-id-sound Γ μ x T
  RenSubDataStructureSound.atomic-rensub-lookup-var-sound ren-data-struct-sound = atomic-ren-var-sound

module AtomicRenSoundM = AtomicRenSubSoundness RenData AtomicRenVar.ren-data-struct ren-data-semantics AtomicRenVarSound.ren-data-struct-sound

open AtomicRenSoundM renaming
  ( tm-arensub-sound to tm-aren-sound
  ; πᵃ-sound to πᵃʳ-sound
  ; liftᵃ-sound to liftᵃʳ-sound
  ; locksᵃ-sound to locksᵃʳ-sound
  )
  using ()
  public

module RenSoundM = RenSubSoundness RenData AtomicRenVar.ren-data-struct ren-data-semantics AtomicRenVarSound.ren-data-struct-sound

open RenSoundM renaming
  ( tm-rensub-sound to tm-ren-sound
  ; liftʳˢ-sound to liftʳ-sound
  ; []ʳˢ-sound to []ʳ-sound
  ; πʳˢ-sound to πʳ-sound
  ; ∷ʳˢ-sound to ∷ʳ-sound
  ; lockʳˢ-sound to lockʳ-sound
  ; ⊚ʳˢ-sound to ⊚ʳ-sound
  )
  using ()
  public


module AtomicSubVarSound where
  open AtomicSubVar
  open TwoCellSoundness

  open M.≅ᵗᵐ-Reasoning

  atomic-sub-var'-sound : {Γ Δ : Ctx n} (Λ : LockTele n m) (σ : AtomicSub Γ Δ) (v : Var x T Δ Λ) →
                          ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧asub ]cl
                                   M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
                            M.≅ᵗᵐ
                          ⟦ atomic-sub-var' Λ σ v ⟧tm
  atomic-sub-var'-sound {T = T} Λ idᵃˢ v =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.id-subst _) ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (
         M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-id ⟦ locksˡᵗ Λ ⟧mod))
                   (M.cl-tm-subst-id (ty-closed-natural T) _)) ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ var-lt-sound Λ v ⟩
      ⟦ var-lt Λ v ⟧tm ∎
  atomic-sub-var'-sound {T = T} Λ (_⊚πᵃˢ {Γ = Γ} {μ = μ} {x = x} {T = S} σ) v =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (⟦ σ ⟧asub M.⊚ M.π) ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (M.symˢ (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _))) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧asub ]cl
               M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (
          M.transˢ (M.⊚-congʳ M.⊚-assoc) (M.transˢ (M.symˢ M.⊚-assoc) (M.transˢ (M.⊚-congˡ (M.isoʳ (,ˡᵗ-sound Λ))) (M.id-subst-unitˡ _)))) ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧asub ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
               M.[ ty-closed-natural T ∣ M.to (,ˡᵗ-sound Λ) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π M.⊚ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (atomic-sub-var'-sound Λ σ v) ⟩
      ⟦ atomic-sub-var' Λ σ v ⟧tm
        M.[ ty-closed-natural T ∣ M.to (,ˡᵗ-sound Λ) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π M.⊚ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (
          M.transˢ (M.⊚-congˡ (M.⊚-congʳ (DRA.lock-fmap-cong ⟦ locksˡᵗ Λ ⟧mod (πᵃʳ-sound Γ μ x S)))) (locksᵃʳ-sound πᵃʳ Λ)) ⟩
      ⟦ atomic-sub-var' Λ σ v ⟧tm M.[ ty-closed-natural T ∣ ⟦ πᵃʳ ,locksᵃʳ⟨ Λ ⟩ ⟧aren ]cl
    ≅⟨ tm-aren-sound (atomic-sub-var' Λ σ v) _ ⟩
      ⟦ (atomic-sub-var' Λ σ v) [ πᵃʳ ,locksᵃʳ⟨ Λ ⟩ ]tmᵃʳ ⟧tm ∎
  atomic-sub-var'-sound {T = T} Λ (σ ,lockᵃˢ⟨ μ ⟩) (vlock v) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
               M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧asub) ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (DRA.key-subst-natural (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))) ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧asub ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-⊚ (ty-closed-natural T) _ ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧asub ]cl
               M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ atomic-sub-var'-sound (lock⟨ μ ⟩, Λ) σ v ⟩
      ⟦ atomic-sub-var' (lock⟨ μ ⟩, Λ) σ v ⟧tm ∎
  atomic-sub-var'-sound {T = T} Λ (keyᵃˢ Θ Ψ α) v =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Ψ) M.⊚ DRA.key-subst ⟦ α ⟧two-cell M.⊚ M.from (,ˡᵗ-sound Θ)) ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (apply-2-cell-var-lt-sound Ψ Θ α v) ⟩
      ⟦ apply-2-cell-var-lt Ψ Θ α v ⟧var M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ var-lt-sound Λ (apply-2-cell-var-lt Ψ Θ α v) ⟩
      ⟦ var-lt Λ (apply-2-cell-var-lt Ψ Θ α v) ⟧tm ∎
  atomic-sub-var'-sound {T = T} Λ (_∷ᵃˢ_/_ {μ = μ} σ t x) (vzero α) =
    begin
      (dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)))
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (⟦ σ ⟧asub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm) ]cl
        M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (DRA.key-subst-natural ⟦ α ⟧two-cell)) ⟩
      (dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)))
        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ μ ⟧mod (⟦ σ ⟧asub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm) ]cl
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (dra-elim-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) _)) ⟩
      dra-elim ⟦ μ ⟧mod
           (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩) M.[ ty-closed-natural ⟨ μ ∣ T ⟩ ∣ ⟦ σ ⟧asub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm ]cl)
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (dra-elim-cong ⟦ μ ⟧mod (M.,cl-β2 (ty-closed-natural ⟨ μ ∣ T ⟩) _ _))) ⟩
      dra-elim ⟦ μ ⟧mod (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm)
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-tm (ty-closed-natural T) (dra-β ⟦ μ ⟧mod _)) ⟩
      ⟦ t ⟧tm
        M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
        M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (M.symˢ (M.⊚-congˡ (M.transˢ (M.⊚-congˡ (M.id-subst-unitˡ _)) (M.id-subst-unitˡ _)))) ⟩
      ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.id-subst _ M.⊚ M.id-subst _ M.⊚ DRA.key-subst ⟦ α ⟧two-cell M.⊚ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ tm-aren-sound t _ ⟩
      ⟦ t [ keyᵃʳ Λ (lock⟨ μ ⟩, ◇) α ]tmᵃʳ ⟧tm ∎
  atomic-sub-var'-sound {T = T} Λ (_∷ᵃˢ_/_ {μ = ρ} {T = S} σ s y) (vsuc v) =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl
               M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (⟦ σ ⟧asub M.,cl⟨ ty-closed-natural ⟨ ρ ∣ S ⟩ ⟩ dra-intro ⟦ ρ ⟧mod ⟦ s ⟧tm) ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (
        M.transˢ (M.symˢ (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _)) (DRA.lock-fmap-cong ⟦ locksˡᵗ Λ ⟧mod (M.,cl-β1 (ty-closed-natural ⟨ ρ ∣ S ⟩) _ _)))) ⟩
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧asub ]cl
               M.[ ty-closed-natural T ∣ M.from (,ˡᵗ-sound Λ) ]cl
    ≅⟨ atomic-sub-var'-sound Λ σ v ⟩
      ⟦ atomic-sub-var' Λ σ v ⟧tm ∎

  atomic-sub-var-sound : (v : Var x T Δ ◇) (σ : AtomicSub Γ Δ) →
                         ⟦ v ⟧var M.[ ty-closed-natural T ∣ ⟦ σ ⟧asub ]cl
                           M.≅ᵗᵐ
                         ⟦ atomic-sub-var v σ ⟧tm
  atomic-sub-var-sound {T = T} v σ =
    begin
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ ⟦ σ ⟧asub ]cl
    ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟨
      ⟦ v ⟧var M.[ ty-closed-natural T ∣ ⟦ σ ⟧asub ]cl
               M.[ ty-closed-natural T ∣ M.id-subst _ ]cl
    ≅⟨ atomic-sub-var'-sound ◇ σ v ⟩
      ⟦ atomic-sub-var' ◇ σ v ⟧tm ∎
    where open M.≅ᵗᵐ-Reasoning

  sub-data-struct-sound : RenSubDataStructureSound SubData sub-data-struct sub-data-semantics
  RenSubDataStructureSound.newV-sound sub-data-struct-sound {x = x} {μ = μ} {T = T} {Γ = Γ} = v0-sound Γ μ x T
  RenSubDataStructureSound.atomic-rensub-lookup-var-sound sub-data-struct-sound = atomic-sub-var-sound

module AtomicSubSoundM = AtomicRenSubSoundness SubData AtomicSubVar.sub-data-struct sub-data-semantics AtomicSubVarSound.sub-data-struct-sound

open AtomicSubSoundM renaming
  ( tm-arensub-sound to tm-asub-sound
  ; πᵃ-sound to πᵃˢ-sound
  ; liftᵃ-sound to liftᵃˢ-sound
  ; locksᵃ-sound to locksᵃˢ-sound
  )
  using ()
  public

module SubSoundM = RenSubSoundness SubData AtomicSubVar.sub-data-struct sub-data-semantics AtomicSubVarSound.sub-data-struct-sound

open SubSoundM renaming
  ( tm-rensub-sound to tm-sub-sound
  ; liftʳˢ-sound to liftˢ-sound
  ; []ʳˢ-sound to []ˢ-sound
  ; πʳˢ-sound to πˢ-sound
  ; ∷ʳˢ-sound to ∷ˢ-sound
  ; lockʳˢ-sound to lockˢ-sound
  ; ⊚ʳˢ-sound to ⊚ˢ-sound
  )
  using ()
  public


lock𝟙-ren-sound : (Γ : Ctx m) → ⟦ lock𝟙-ren {Γ = Γ} ⟧ren M.≅ˢ M.id-subst _
lock𝟙-ren-sound Γ =
  M.transˢ (M.⊚-congʳ (M.id-subst-unitʳ _)) (M.transˢ (M.id-subst-unitʳ _) (M.transˢ (M.id-subst-unitˡ _) (DRA.key-subst-eq ⟦id-cell⟧-sound)))

unlock𝟙-ren-sound : (Γ : Ctx m) → ⟦ unlock𝟙-ren {Γ = Γ} ⟧ren M.≅ˢ M.id-subst _
unlock𝟙-ren-sound Γ =
  M.transˢ (M.id-subst-unitʳ _) (M.transˢ (M.⊚-congˡ (M.id-subst-unitˡ _)) (M.transˢ (M.id-subst-unitˡ _) (DRA.key-subst-eq ⟦id-cell⟧-sound)))

fuselocks-ren-sound : (μ : Modality n o) (ρ : Modality m n) (Γ : Ctx o) →
                      ⟦ fuselocks-ren {Γ = Γ} {μ = μ} {ρ = ρ} ⟧ren M.≅ˢ DRA.key-subst (to (⟦ⓜ⟧-sound μ ρ))
fuselocks-ren-sound μ ρ Γ =
  M.transˢ (M.⊚-congʳ (M.id-subst-unitʳ _)) (
  M.transˢ (M.id-subst-unitʳ _) (
  M.transˢ (M.⊚-congʳ (DRA.key-subst-eq ⟦id-cell⟧-sound)) (
  M.transˢ (M.id-subst-unitʳ _) (
  M.transˢ (M.⊚-congˡ (M.id-subst-unitˡ _)) (
  M.id-subst-unitˡ _)))))

unfuselocks-ren-sound : (μ : Modality n o) (ρ : Modality m n) (Γ : Ctx o) →
                        ⟦ unfuselocks-ren {Γ = Γ} {μ = μ} {ρ = ρ} ⟧ren M.≅ˢ DRA.key-subst (from (⟦ⓜ⟧-sound μ ρ))
unfuselocks-ren-sound μ ρ Γ =
  M.transˢ (M.⊚-congʳ (M.transˢ (M.⊚-congʳ (M.id-subst-unitʳ _)) (M.id-subst-unitʳ _))) (
  M.transˢ (M.⊚-congˡ (M.transˢ (M.⊚-congˡ (M.id-subst-unitˡ _)) (M.id-subst-unitˡ _))) (
  M.transˢ (M.⊚-congˡ (DRA.key-subst-eq ⟦id-cell⟧-sound)) (
  M.id-subst-unitˡ _)))

lock𝟙-tm-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) → ⟦ lock𝟙-tm t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm
lock𝟙-tm-sound {Γ = Γ} {T = T} t =
  M.transᵗᵐ (M.symᵗᵐ (tm-ren-sound t lock𝟙-ren)) (
  M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (lock𝟙-ren-sound Γ)) (
  M.cl-tm-subst-id (ty-closed-natural T) _))

fuselocks-tm-sound : (μ : Modality n o) (ρ : Modality m n) {Γ : Ctx o} {T : Ty m}
                     (t : Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T) →
                     ⟦ fuselocks-tm t ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound μ ρ)) ]cl
fuselocks-tm-sound μ ρ {Γ} {T} t =
  M.transᵗᵐ (M.symᵗᵐ (tm-ren-sound t fuselocks-ren))
            (M.cl-tm-subst-cong-subst (ty-closed-natural T) (fuselocks-ren-sound μ ρ Γ))

∙¹-sound : {Γ : Ctx m} {A B : Ty m} (f : Tm Γ (A ⇛ B)) (a : Tm Γ A) →
           ⟦ f ∙¹ a ⟧tm M.≅ᵗᵐ M.app ⟦ f ⟧tm ⟦ a ⟧tm
∙¹-sound f a = M.app-cong M.reflᵗᵐ (lock𝟙-tm-sound a)

/cl-sound : {Γ : Ctx m} {μ : Modality n m} {T : Ty n} (t : Tm (Γ ,lock⟨ μ ⟩) T) (x : Name) →
            (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm) M./cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩
              M.≅ˢ
            ⟦ t / x ⟧sub
/cl-sound t x = ∷ˢ-sound idˢ t x

/v-sound : {Γ : Ctx m} {T : Ty m} (t : Tm Γ T) (x : Name) →
           (⟦ t ⟧tm M./v) M.≅ˢ ⟦ lock𝟙-tm t / x ⟧sub
/v-sound {T = T} t x =
  M.transˢ (M./v-/cl (ty-closed-natural T) ⟦ t ⟧tm) (
  M.transˢ (M.symˢ (M.,cl-cong-cl (𝟙-preserves-cl (ty-closed-natural T)))) (
  M.transˢ (M.symˢ (M.,cl-cong-tm (ty-closed-natural ⟨ 𝟙 ∣ T ⟩) (lock𝟙-tm-sound t))) (
  /cl-sound (lock𝟙-tm t) x)))

keyʳ-sound-cod : {μ : Modality m n} (Λ : LockTele n m) (α : TwoCell μ (locksˡᵗ Λ)) {Γ : Ctx n} →
                 DRA.key-subst ⟦ α ⟧two-cell M.⊚ M.from (,ˡᵗ-sound {Γ = Γ} Λ) M.≅ˢ ⟦ keyʳ Λ (lock⟨ μ ⟩, ◇) α ⟧ren
keyʳ-sound-cod Λ α = M.symˢ (M.⊚-congˡ (M.transˢ (M.⊚-congˡ (M.id-subst-unitˡ _)) (M.id-subst-unitˡ _)))

keyʳ-sound : {μ ρ : Modality m n} (α : TwoCell μ ρ) {Γ : Ctx n} →
             DRA.key-subst ⟦ α ⟧two-cell M.≅ˢ ⟦ keyʳ {Γ = Γ} (lock⟨ ρ ⟩, ◇) (lock⟨ μ ⟩, ◇) α ⟧ren
keyʳ-sound {ρ = ρ} α {Γ} =
  M.transˢ (M.symˢ (M.transˢ (M.⊚-congʳ (M.id-subst-unitʳ _)) (M.id-subst-unitʳ _))) (keyʳ-sound-cod (lock⟨ ρ ⟩, ◇) α {Γ})

weaken-tm-sound : (Γ : Ctx m) (x : Name) (μ : Modality n m) (S : Ty n) {T : Ty m} (t : Tm Γ T) →
                  ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.π ]cl M.≅ᵗᵐ ⟦ weaken-tm {μ = μ} {x} {S} t ⟧tm
weaken-tm-sound Γ x μ S {T} t = M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (πʳ-sound Γ μ x S)) (tm-ren-sound t πʳ)

,ˡᵗ-sound-to-naturalʳ : (Λ : LockTele m n) {Γ Δ : Ctx m} (σ : Ren Γ Δ) →
                        M.to (,ˡᵗ-sound Λ) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ⟧ren
                          M.≅ˢ
                        ⟦ σ ,locksʳ⟨ Λ ⟩ ⟧ren M.⊚ M.to (,ˡᵗ-sound Λ)
,ˡᵗ-sound-to-naturalʳ ◇ σ = M.transˢ (M.id-subst-unitˡ _) (M.symˢ (M.id-subst-unitʳ _))
,ˡᵗ-sound-to-naturalʳ (lock⟨ μ ⟩, Λ) σ =
  begin
    M.to (,ˡᵗ-sound Λ) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧ren
  ≅⟨ M.⊚-assoc ⟩
    M.to (,ˡᵗ-sound Λ) M.⊚ (DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ (lock⟨ μ ⟩, Λ) ⟧mod ⟦ σ ⟧ren)
  ≅⟨ M.⊚-congʳ (DRA.key-subst-natural (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))) ⟩
    M.to (,ˡᵗ-sound Λ) M.⊚ (DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧ren) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
  ≅⟨ M.⊚-congʳ (M.⊚-congˡ (DRA.lock-fmap-cong ⟦ locksˡᵗ Λ ⟧mod (lockʳ-sound σ μ))) ⟩
    M.to (,ˡᵗ-sound Λ) M.⊚ (DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ,lockʳ⟨ μ ⟩ ⟧ren M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))
  ≅⟨ M.⊚-assoc ⟨
    (M.to (,ˡᵗ-sound Λ) M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod ⟦ σ ,lockʳ⟨ μ ⟩ ⟧ren) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))
  ≅⟨ M.⊚-congˡ (,ˡᵗ-sound-to-naturalʳ Λ (σ ,lockʳ⟨ μ ⟩)) ⟩
    (⟦ σ ,lockʳ⟨ μ ⟩ ,locksʳ⟨ Λ ⟩ ⟧ren M.⊚ M.to (,ˡᵗ-sound Λ)) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))
  ≅⟨ M.⊚-assoc ⟩
    ⟦ σ ,lockʳ⟨ μ ⟩ ,locksʳ⟨ Λ ⟩ ⟧ren M.⊚ (M.to (,ˡᵗ-sound Λ) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))) ∎
  where open M.≅ˢ-Reasoning
