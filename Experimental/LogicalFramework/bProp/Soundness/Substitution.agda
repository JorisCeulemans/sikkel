open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics using (bPropExtSem)

module Experimental.LogicalFramework.bProp.Soundness.Substitution
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.List
open import Data.Product
open import Data.Unit.Polymorphic

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy) using ()
open import Model.DRA as DRA using (dra-natural; dra-cong)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.MSTT.Soundness.Substitution 𝒫
open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧
open Experimental.LogicalFramework.Parameter.bPropExtensionSemantics ℳ 𝒯 𝓉 hiding (bPropExtSem)
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯

open bPropExtSem ⟦𝒷⟧

private variable
  m : Mode
  Γ Δ : Ctx m


module bPropTraversalSoundness
  (Trav : ∀ {m} → Ctx m → Ctx m → Set)
  (trav-struct : TravStruct Trav)
  (trav-struct-sound : TravStructSoundness trav-struct)
  where

  open TravStruct trav-struct
  open TravStructSoundness trav-struct-sound
  open bPropTraversal Trav trav-struct

  traverse-bprop-sound : (φ : bProp Δ) (σ : Trav Γ Δ) →
                         ⟦ φ ⟧bprop M.[ ⟦ σ ⟧trav ] M.≅ᵗʸ ⟦ traverse-bprop φ σ ⟧bprop
  traverse-ext-bpargs-sound : ∀ {arginfos} (args : ExtBPArgs arginfos Δ) (σ : Trav Γ Δ) →
                              semprops-subst ⟦ args ⟧bpextargs ⟦ σ ⟧trav
                                ≅ᵇᵖˢ
                              ⟦ traverse-ext-bpargs args σ ⟧bpextargs

  traverse-bprop-sound ⊤ᵇ σ = M.Const-natural _ ⟦ σ ⟧trav
  traverse-bprop-sound ⊥ᵇ σ = M.Const-natural _ ⟦ σ ⟧trav
  traverse-bprop-sound (_≡ᵇ_ {T = T} t1 t2) σ =
    M.transᵗʸ (M.Id-cl-natural (ty-closed-natural T) ⟦ σ ⟧trav) (M.Id-cong' (traverse-tm-sound t1 σ) (traverse-tm-sound t2 σ))
  traverse-bprop-sound (⟨ μ ∣ φ ⟩⊃ ψ) σ =
    M.transᵗʸ (M.⇛-natural ⟦ σ ⟧trav)
              (M.⇛-cong (M.transᵗʸ (dra-natural ⟦ μ ⟧mod ⟦ σ ⟧trav)
                                   (dra-cong ⟦ μ ⟧mod (M.transᵗʸ (M.ty-subst-cong-subst (lock-sound σ μ) _) (traverse-bprop-sound φ (lock σ)))))
                        (traverse-bprop-sound ψ σ))
  traverse-bprop-sound (φ ∧ ψ) σ =
    M.transᵗʸ (M.⊠-natural ⟦ σ ⟧trav) (M.⊠-cong (traverse-bprop-sound φ σ) (traverse-bprop-sound ψ σ))
  traverse-bprop-sound (∀[ μ ∣ x ∈ T ] φ) σ =
    M.transᵗʸ (M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) ⟦ σ ⟧trav)
              (M.Pi-cong-cod (M.transᵗʸ (M.ty-subst-cong-subst (lift-sound {μ = μ} {x = x} {T = T} σ) _)
                                        (traverse-bprop-sound φ (lift σ))))
  traverse-bprop-sound ⟨ μ ∣ φ ⟩ σ =
    M.transᵗʸ (dra-natural ⟦ μ ⟧mod ⟦ σ ⟧trav)
              (dra-cong ⟦ μ ⟧mod (M.transᵗʸ (M.ty-subst-cong-subst (lock-sound σ μ) _) (traverse-bprop-sound φ (lock σ))))
  traverse-bprop-sound (ext c tmargs bpargs) σ =
    M.transᵗʸ (apply-sem-prop-constructor-natural ⟦ c ⟧bp-code ⟦ σ ⟧trav (⟦⟧bp-code-natural c) ⟦ tmargs ⟧tmextargs ⟦ bpargs ⟧bpextargs)
              (apply-sem-prop-constructor-cong ⟦ c ⟧bp-code (⟦⟧bp-code-cong c) (traverse-ext-tmargs-sound tmargs σ) (traverse-ext-bpargs-sound bpargs σ))

  traverse-ext-bpargs-sound {arginfos = []}          _ σ = tt
  traverse-ext-bpargs-sound {arginfos = arginfo ∷ _} (arg , args) σ =
    M.transᵗʸ (M.ty-subst-cong-subst (lift-trav-tel-sound σ (arg-tel arginfo)) _) (traverse-bprop-sound arg _)
    ,
    traverse-ext-bpargs-sound args σ


module bPropRenSubSoundness
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  (⟦_⟧rensubdata : RenSubDataSemantics V)
  (rensub-struct-sound : RenSubDataStructureSound V rensub-struct ⟦_⟧rensubdata)
  where

  open AtomicRenSub V rensub-struct
  open RenSub V rensub-struct
  open RenSubSemantics V ⟦_⟧rensubdata
  open AtomicRenSubSoundness V rensub-struct ⟦_⟧rensubdata rensub-struct-sound

  open bPropRenSub V rensub-struct
  open bPropTraversalSoundness AtomicRenSub AtomicRenSubTrav AtomicRenSubTravSound

  bprop-arensub-sound : (φ : bProp Δ) (σ : AtomicRenSub Γ Δ) →
                        ⟦ φ ⟧bprop M.[ ⟦ σ ⟧arensub ] M.≅ᵗʸ ⟦ φ [ σ ]bpropᵃ ⟧bprop
  bprop-arensub-sound = traverse-bprop-sound

  bprop-rensub-sound : (φ : bProp Δ) (σ : RenSub Γ Δ) →
                       ⟦ φ ⟧bprop M.[ ⟦ σ ⟧rensub ] M.≅ᵗʸ ⟦ φ [ σ ]bpropʳˢ ⟧bprop
  bprop-rensub-sound φ id = M.ty-subst-id _
  bprop-rensub-sound φ (id ⊚a τᵃ) = bprop-arensub-sound φ τᵃ
  bprop-rensub-sound φ (σ@(_ ⊚a _) ⊚a τᵃ) =
    M.transᵗʸ (M.symᵗʸ (M.ty-subst-comp _ _ _))
              (M.transᵗʸ (M.ty-subst-cong-ty _ (bprop-rensub-sound φ σ)) (bprop-arensub-sound (φ [ σ ]bpropʳˢ) τᵃ))


module bPropRenSoundness = bPropRenSubSoundness RenData AtomicRenVar.ren-data-struct ren-data-semantics AtomicRenVarSound.ren-data-struct-sound
open bPropRenSoundness renaming
  ( bprop-arensub-sound to bprop-aren-sound
  ; bprop-rensub-sound to bprop-ren-sound
  ) public

module bPropSubSoundness = bPropRenSubSoundness SubData AtomicSubVar.sub-data-struct sub-data-semantics AtomicSubVarSound.sub-data-struct-sound
open bPropSubSoundness renaming
  ( bprop-arensub-sound to bprop-asub-sound
  ; bprop-rensub-sound to bprop-sub-sound
  ) public
