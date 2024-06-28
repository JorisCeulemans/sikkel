--------------------------------------------------
-- Extraction of MSTT contexts, types, programs to Agda types and
-- programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT.Extraction
  (𝒫 : MSTT-Parameter)
  where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product renaming (_,_ to [_,_])
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Unit
open import Function
open import Function.Consequences.Setoid
open import Function.Construct.Composition
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open MSTT-Parameter 𝒫
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉 hiding (refl)
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ 𝒯 𝓉 ⟦𝓉⟧

open import Model.Helpers
import Model.BaseCategory as M
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; tm-setoid to semtm-setoid) using ()
import Model.Type.Function as M

private variable
  m n : Mode
  μ ρ : Modality m n
  Γ Δ : Ctx m
  T S : Ty m


--------------------------------------------------
-- Definition of extractability for MSTT contexts and types at the
-- trivial mode

-- To make an MSTT context extractable, we need to provide an Agda
-- type and an isomorphism between that type and the context's
-- denotation as a presheaf over the trivial base category.
record ExtractableCtx (Γ : Ctx ★) : Set₁ where
  no-eta-equality
  field
    AgdaCtx : Set
    extract-ctx-iso : (⟦ Γ ⟧ctx M.⟨ tt ⟩) ↔ AgdaCtx

open ExtractableCtx {{...}} public

extract-ctx : (Γ : Ctx ★) → {{ExtractableCtx Γ}} → Set
extract-ctx Γ {{exΓ}} = AgdaCtx


-- The definition of extractability for MSTT types is more or less the
-- same as for contexts.
record ExtractableTy (T : Ty ★) : Set₁ where
  no-eta-equality
  field
    AgdaTy : Set
    extract-ty-iso-◇ : ((⟦ T ⟧ty {M.◇}) M.⟨ tt , tt ⟩) ↔ AgdaTy

  extract-ty-iso : {sΓ : SemCtx M.★} {γ : sΓ M.⟨ tt ⟩} →
                   ((⟦ T ⟧ty {sΓ}) M.⟨ tt , γ ⟩) ↔ AgdaTy
  extract-ty-iso = extract-ty-iso-◇ ↔-∘ M.closed-ty-cell-iso-◇ (ty-closed-natural T) _ _

  extract-ty-iso-transport : {sΓ : SemCtx M.★} {γ γ' : sΓ M.⟨ tt ⟩} (eγ : γ ≡ γ') →
                             (t : (⟦ T ⟧ty {sΓ}) M.⟨ tt , γ ⟩) →
                             Inverse.from extract-ty-iso (Inverse.to extract-ty-iso t) ≡ ⟦ T ⟧ty M.⟪ tt , trans (M.ctx-id sΓ) eγ ⟫ t
  extract-ty-iso-transport {sΓ} eγ t =
    trans (cong (Inverse.from (M.closed-ty-cell-iso-◇ (ty-closed-natural T) _ _)) (Inverse.strictlyInverseʳ extract-ty-iso-◇ _)) (
    trans (sym (M.ty-id ⟦ T ⟧ty)) (
    trans (M.naturality (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ sΓ)))) (
    trans (cong (Inverse.from (M.closed-ty-cell-iso-◇ (ty-closed-natural T) _ _))
                (trans (M.ty-cong ⟦ T ⟧ty refl) (M.naturality (M.to (M.closed-natural (ty-closed-natural T) (M.!◇ sΓ)))))) (
    M.eq (M.isoʳ (M.closed-natural (ty-closed-natural T) (M.!◇ sΓ))) _))))

open ExtractableTy {{...}} public

extract-ty : (T : Ty ★) → {{ExtractableTy T}} → Set
extract-ty T {{exT}} = AgdaTy


--------------------------------------------------
-- Given an extractable context Γ and extractable type T, there is an
-- Agda isomorphism between SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty and
-- (extract-ctx Γ → extract-ctx T). This allows us to extract MSTT
-- terms of type T.

module ExtractTm
  {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
  {T : Ty ★} {{_ : ExtractableTy T}}
  where

  tm-extraction-setoid : Setoid _ _
  tm-extraction-setoid = extract-ctx Γ →-setoid extract-ty T

  extract-semtm : SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty → extract-ctx Γ → extract-ty T
  extract-semtm t =
    Inverse.to extract-ty-iso
    ∘ t M.⟨ tt ,_⟩'
    ∘ Inverse.from extract-ctx-iso

  extract-semtm-cong : {t1 t2 : SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty} → t1 M.≅ᵗᵐ t2 →
                       (γ : extract-ctx Γ) →
                       extract-semtm t1 γ ≡ extract-semtm t2 γ
  extract-semtm-cong 𝒆 γ = cong (Inverse.to extract-ty-iso) (M.eq 𝒆 _)

  embed-semtm : (extract-ctx Γ → extract-ty T) → SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
  embed-semtm f M.⟨ x , γ ⟩' = Inverse.from extract-ty-iso (f (Inverse.to extract-ctx-iso γ))
  M.naturality (embed-semtm f) tt eγ =
    trans (M.naturality (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ ⟦ Γ ⟧ctx))))
          (cong (M.func (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ ⟦ Γ ⟧ctx))))
                (trans (M.strong-ty-id ⟦ T ⟧ty)
                       (cong (Inverse.from extract-ty-iso-◇ ∘ f ∘ Inverse.to extract-ctx-iso) (trans (sym (M.ctx-id ⟦ Γ ⟧ctx)) eγ))))

  embed-semtm-cong : {f g : extract-ctx Γ → extract-ty T} → ((γ : extract-ctx Γ) → f γ ≡ g γ) →
                     embed-semtm f M.≅ᵗᵐ embed-semtm g
  M.eq (embed-semtm-cong e) γ = cong (Inverse.from extract-ty-iso) (e _)

  extract-embed-semtm : (f : extract-ctx Γ → extract-ty T) (γ : extract-ctx Γ) →
                        extract-semtm (embed-semtm f) γ ≡ f γ
  extract-embed-semtm f γ =
    trans (Inverse.strictlyInverseˡ extract-ty-iso _) (cong f (Inverse.strictlyInverseˡ (extract-ctx-iso) γ))

  embed-extract-semtm : (t : SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty) → embed-semtm (extract-semtm t) M.≅ᵗᵐ t
  M.eq (embed-extract-semtm t) γ =
    trans (extract-ty-iso-transport (Inverse.strictlyInverseʳ extract-ctx-iso _) _) (M.naturality t tt _)

  extract-semtm-iso : Inverse (semtm-setoid ⟦ Γ ⟧ctx ⟦ T ⟧ty) tm-extraction-setoid
  Inverse.to extract-semtm-iso = extract-semtm
  Inverse.from extract-semtm-iso = embed-semtm
  Inverse.to-cong extract-semtm-iso = extract-semtm-cong
  Inverse.from-cong extract-semtm-iso = embed-semtm-cong
  Inverse.inverse extract-semtm-iso =
    [ strictlyInverseˡ⇒inverseˡ (semtm-setoid ⟦ Γ ⟧ctx ⟦ T ⟧ty) tm-extraction-setoid {f⁻¹ = embed-semtm} extract-semtm-cong extract-embed-semtm
    , strictlyInverseʳ⇒inverseʳ (semtm-setoid ⟦ Γ ⟧ctx ⟦ T ⟧ty) tm-extraction-setoid embed-semtm-cong embed-extract-semtm
    ]

  extract-tm : Tm Γ T → extract-ctx Γ → extract-ty T
  extract-tm t = extract-semtm ⟦ t ⟧tm

open ExtractTm public


--------------------------------------------------
-- Instances of extractability for many of the MSTT type formers and
-- context constructors.

instance
  ◇-extractable : ExtractableCtx ◇
  ExtractableCtx.AgdaCtx ◇-extractable = ⊤
  ExtractableCtx.extract-ctx-iso ◇-extractable =
    mk↔ₛ′ (λ _ → tt) (λ _ → tt) (λ _ → refl) (λ _ → refl)

  ,,-extractable : {Γ : Ctx ★} → {{ExtractableCtx Γ}} →
                   {T : Ty ★} → {{ExtractableTy T}} →
                   {x : Name} →
                   ExtractableCtx (Γ ,, 𝟙 ∣ x ∈ T)
  ExtractableCtx.AgdaCtx (,,-extractable {Γ} {T}) = extract-ctx Γ × extract-ty T
  ExtractableCtx.extract-ctx-iso (,,-extractable {Γ} {T}) = mk↔ₛ′
    (map (Inverse.to extract-ctx-iso) (Inverse.to extract-ty-iso))
    (map (Inverse.from extract-ctx-iso) (Inverse.from extract-ty-iso))
    (λ _ → cong₂ [_,_] (Inverse.strictlyInverseˡ (extract-ctx-iso {Γ}) _) (Inverse.strictlyInverseˡ extract-ty-iso _))
    (λ _ → M.to-Σ-ty-eq ⟦ T ⟧ty (Inverse.strictlyInverseʳ extract-ctx-iso _)
                                (trans (cong (⟦ T ⟧ty M.⟪ tt , _ ⟫_) (extract-ty-iso-transport (sym (Inverse.strictlyInverseʳ extract-ctx-iso _)) _))
                                       (trans (sym (M.ty-comp ⟦ T ⟧ty)) (M.strong-ty-id ⟦ T ⟧ty))))

  lock𝟙-extractable : {Γ : Ctx ★} → {{ExtractableCtx Γ}} →
                      ExtractableCtx (Γ ,lock⟨ 𝟙 ⟩)
  ExtractableCtx.AgdaCtx (lock𝟙-extractable {Γ}) = extract-ctx Γ
  ExtractableCtx.extract-ctx-iso (lock𝟙-extractable {Γ}) = extract-ctx-iso {Γ}

  Nat'-extractable : ExtractableTy Nat'
  ExtractableTy.AgdaTy Nat'-extractable = ℕ
  ExtractableTy.extract-ty-iso-◇ Nat'-extractable = ↔-id ℕ

  Bool'-extractable : ExtractableTy Bool'
  ExtractableTy.AgdaTy Bool'-extractable = Bool
  ExtractableTy.extract-ty-iso-◇ Bool'-extractable = ↔-id Bool

to-★-pshfun : {sT sS : SemTy {M.★} M.◇} →
              (sT M.⟨ tt , tt ⟩ → sS M.⟨ tt , tt ⟩) →
              M.PshFun sT sS tt tt
to-★-pshfun f M.$⟨ _ , _ ⟩ t = f t
M.naturality (to-★-pshfun {sT} {sS} f) = trans (cong f (M.strong-ty-id sT)) (sym (M.strong-ty-id sS))

instance
  ⇛-extractable : {T S : Ty ★} → {{ExtractableTy T}} → {{ExtractableTy S}} →
                  ExtractableTy (T ⇛ S)
  ExtractableTy.AgdaTy (⇛-extractable {T} {S}) = extract-ty T → extract-ty S
  ExtractableTy.extract-ty-iso-◇ (⇛-extractable {T} {S}) = mk↔ₛ′
    (λ psh-f t → Inverse.to (extract-ty-iso-◇ {S}) (psh-f M.$⟨ tt , refl ⟩ Inverse.from (extract-ty-iso-◇ {T}) t))
    (λ f → to-★-pshfun (Inverse.from (extract-ty-iso-◇ {S}) ∘ f ∘ Inverse.to (extract-ty-iso-◇ {T})))
    (λ f → funext λ _ → trans (Inverse.strictlyInverseˡ (extract-ty-iso-◇ {S}) _) (cong f (Inverse.strictlyInverseˡ (extract-ty-iso-◇ {T}) _)))
    (λ psh-f → M.to-pshfun-eq (λ { _ refl _ → trans (Inverse.strictlyInverseʳ (extract-ty-iso-◇ {S}) _)
                                                    (cong (psh-f M.$⟨ tt , refl ⟩_) (Inverse.strictlyInverseʳ (extract-ty-iso-◇ {T}) _)) }))

  ⊠-extractable : {T S : Ty ★} → {{ExtractableTy T}} → {{ExtractableTy S}} →
                 ExtractableTy (T ⊠ S)
  ExtractableTy.AgdaTy (⊠-extractable {T} {S}) = extract-ty T × extract-ty S
  ExtractableTy.extract-ty-iso-◇ (⊠-extractable {T} {S}) = extract-ty-iso-◇ {T} ×-↔ extract-ty-iso-◇ {S}

  mod𝟙-extractable : {T : Ty ★} → {{ExtractableTy T}} → ExtractableTy ⟨ 𝟙 ∣ T ⟩
  ExtractableTy.AgdaTy (mod𝟙-extractable {T}) = extract-ty T
  ExtractableTy.extract-ty-iso-◇ (mod𝟙-extractable {T}) = extract-ty-iso-◇ {T}


-- Convenient function to extract terms that live in the empty context.
extract-tm-◇ : {T : Ty ★} → {{_ : ExtractableTy T}} → Tm ◇ T → extract-ty T
extract-tm-◇ t = extract-tm t tt
