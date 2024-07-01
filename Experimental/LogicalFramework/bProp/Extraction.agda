--------------------------------------------------
-- Extraction of bProps
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.bProp.Extraction
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.Empty
open import Data.Product renaming (_,_ to [_,_])
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Unit
open import Function
open import Function.Construct.Composition
open import Function.Construct.Identity
open import Relation.Binary.PropositionalEquality

open import Model.Helpers
import Model.BaseCategory as M
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; tm-setoid to semtm-setoid) using ()
import Model.Type.Function as M
import Experimental.DependentTypes.Model.Function as Π

open import Experimental.LogicalFramework.MSTT 𝒫 hiding (refl)
open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n : Mode
  μ ρ : Modality m n
  Γ Δ : Ctx m
  T S : Ty m


--------------------------------------------------
-- Definition of extractability for BiSikkel propositions

-- A bProp in an extractable MSTT context Γ is extractable if it is
-- isomorphic to an Agda type family over extract-ctx Γ.
record ExtractableProp {Γ : Ctx ★} {{exΓ : ExtractableCtx Γ}} (φ : bProp Γ) : Set₁ where
  no-eta-equality
  field
    AgdaProp : extract-ctx Γ → Set
    extract-prop-iso : (γ : extract-ctx Γ) →
                       (⟦ φ ⟧bprop M.⟨ tt , Inverse.from (extract-ctx-iso {Γ}) γ ⟩) ↔ AgdaProp γ

  extract-prop-iso' : (γ : ⟦ Γ ⟧ctx M.⟨ tt ⟩) →
                      (⟦ φ ⟧bprop M.⟨ tt , γ ⟩) ↔ AgdaProp (Inverse.to (extract-ctx-iso {Γ}) γ)
  extract-prop-iso' γ =
    extract-prop-iso _
    ↔-∘
    M.ty-ctx-subst-iso ⟦ φ ⟧bprop (sym (Inverse.strictlyInverseʳ (extract-ctx-iso {Γ}) γ))

open ExtractableProp {{...}} public

extract-bprop : {Γ : Ctx ★} → {{_ : ExtractableCtx Γ}} →
                (φ : bProp Γ) → {{ExtractableProp φ}} →
                extract-ctx Γ → Set
extract-bprop φ = AgdaProp


--------------------------------------------------
-- Instances of extractability for many BiSikkel bProp constructors

-- Lemma for the ≡ᵇ instance
cancel-iso-to : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (r : A ↔ B)
                {x y : A} →
                Inverse.to r x ≡ Inverse.to r y →
                x ≡ y
cancel-iso-to r {x} {y} e =
  trans (sym (Inverse.strictlyInverseʳ r x)) (
  trans (cong (Inverse.from r) e) (
  Inverse.strictlyInverseʳ r y))

module Instances
  {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
  where

  instance
    ⊤ᵇ-extractable : ExtractableProp {Γ} ⊤ᵇ
    ExtractableProp.AgdaProp ⊤ᵇ-extractable _ = ⊤
    ExtractableProp.extract-prop-iso ⊤ᵇ-extractable _ = ↔-id ⊤

    ⊥ᵇ-extractable : ExtractableProp {Γ} ⊥ᵇ
    ExtractableProp.AgdaProp ⊥ᵇ-extractable _ = ⊥
    ExtractableProp.extract-prop-iso ⊥ᵇ-extractable _ = ↔-id ⊥

    ≡ᵇ-extractable : {T : Ty ★} → {{ExtractableTy T}} →
                     {t1 t2 : Tm Γ T} →
                     ExtractableProp (t1 ≡ᵇ t2)
    ExtractableProp.AgdaProp (≡ᵇ-extractable {t1 = t1} {t2}) γ =
      extract-tm t1 γ ≡ extract-tm t2 γ
    ExtractableProp.extract-prop-iso (≡ᵇ-extractable {T}) γ = mk↔ₛ′
      (cong (Inverse.to (extract-ty-iso {T})))
      (cancel-iso-to (extract-ty-iso {T}))
      (λ _ → uip _ _)
      (λ _ → uip _ _)

  to-★-pshfun : {sΓ : SemCtx M.★} {sT sS : SemTy sΓ} {γ : sΓ M.⟨ tt ⟩} →
                (sT M.⟨ tt , γ ⟩ → sS M.⟨ tt , γ ⟩) →
                M.PshFun sT sS tt γ
  (to-★-pshfun {sΓ} {sT} {sS} f) M.$⟨ tt , eγ ⟩ t = sS M.⟪ tt , eγ ⟫ f (M.ty-ctx-subst sT (trans (sym eγ) (M.ctx-id sΓ)) t)
  M.naturality (to-★-pshfun {sΓ} {sT} {sS} f) = trans (cong (sS M.⟪ tt , _ ⟫_) (cong f (sym (M.strong-ty-comp sT)))) (M.strong-ty-comp sS)

  instance
    ⊃-extractable : {φ : bProp (Γ ,lock⟨ 𝟙 ⟩)} → {{ExtractableProp φ}} →
                    {ψ : bProp Γ} → {{ExtractableProp ψ}} →
                    ExtractableProp (⟨ 𝟙 ∣ φ ⟩⊃ ψ)
    ExtractableProp.AgdaProp (⊃-extractable {φ} {ψ}) γ = extract-bprop φ γ → extract-bprop ψ γ
    ExtractableProp.extract-prop-iso (⊃-extractable {φ} {ψ}) γ = mk↔ₛ′
      (λ psh-f evφ → Inverse.to (extract-prop-iso {φ = ψ} γ) (psh-f M.$⟨ tt , M.ctx-id ⟦ Γ ⟧ctx ⟩ Inverse.from (extract-prop-iso {φ = φ} γ) evφ))
      (λ f → to-★-pshfun (Inverse.from (extract-prop-iso {φ = ψ} γ) ∘ f ∘ Inverse.to (extract-prop-iso {φ = φ} γ)))
      (λ f → funext λ _ → trans (cong (Inverse.to (extract-prop-iso {φ = ψ} γ)) (M.ty-id ⟦ ψ ⟧bprop)) (
                          trans (Inverse.strictlyInverseˡ (extract-prop-iso {φ = ψ} γ) _) (cong f (
                          trans (cong (Inverse.to (extract-prop-iso {φ = φ} γ)) (M.strong-ty-id ⟦ φ ⟧bprop)) (
                          Inverse.strictlyInverseˡ (extract-prop-iso {φ = φ} γ) _)))))
      (λ psh-f → M.to-pshfun-eq (λ _ eγ evφ →
        trans (cong (⟦ ψ ⟧bprop M.⟪ tt , eγ ⟫_) (Inverse.strictlyInverseʳ (extract-prop-iso {φ = ψ} γ) _)) (
        trans (sym (M.naturality psh-f)) (
        trans (M.$-cong psh-f refl) (cong (psh-f M.$⟨ tt , eγ ⟩_) (
        trans (cong (⟦ φ ⟧bprop M.⟪ tt , eγ ⟫_) (Inverse.strictlyInverseʳ (extract-prop-iso {φ = φ} γ) _)) (
        trans (sym (M.ty-comp ⟦ φ ⟧bprop)) (
        M.strong-ty-id ⟦ φ ⟧bprop))))))))

    ∧-extractable : {φ : bProp Γ} → {{ExtractableProp φ}} →
                    {ψ : bProp Γ} → {{ExtractableProp ψ}} →
                    ExtractableProp (φ ∧ ψ)
    ExtractableProp.AgdaProp (∧-extractable {φ} {ψ = ψ}) γ = extract-bprop φ γ × extract-bprop ψ γ
    ExtractableProp.extract-prop-iso (∧-extractable {φ} {ψ = ψ}) γ = extract-prop-iso {φ = φ} γ ×-↔ extract-prop-iso {φ = ψ} γ

  to-★-Π-pshfun : {sΓ : SemCtx M.★} {sT : SemTy sΓ} {sS : SemTy (sΓ M.,, sT)} {γ : sΓ M.⟨ tt ⟩} →
                  ((t : sT M.⟨ tt , γ ⟩) → sS M.⟨ tt , [ γ , t ] ⟩) →
                  Π.PshFun sT sS tt γ
  (to-★-Π-pshfun {sΓ} {sT} {sS} f) Π.$⟨ tt , eγ ⟩ t =
    sS M.⟪ tt , M.to-Σ-ty-eq sT eγ (trans (sym (trans (M.ty-comp sT) (M.ty-comp sT))) (M.strong-ty-id sT)) ⟫
      f (M.ty-ctx-subst sT (trans (sym eγ) (M.ctx-id sΓ)) t)
  Π.naturality (to-★-Π-pshfun {sΓ} {sT} {sS} f) =
    trans (cong (sS M.⟪ _ , _ ⟫_) (sym (dcong f (M.strong-ty-comp sT)))) (
    trans (cong (sS M.⟪ _ , _ ⟫_) (M.PropositionalEquality.ty-ctx-ext-prop-eq-subst sS (M.strong-ty-comp sT) _)) (
    M.ty-cong-2-2 sS refl))

  extract-prop-iso-from-subst : {T : Ty ★} {{_ : ExtractableTy T}}
                                {x : Name} {φ : bProp (Γ ,, 𝟙 ∣ x ∈ T)} {{_ : ExtractableProp φ}}
                                {γ : extract-ctx Γ} {t1 t2 : extract-ty T} →
                                (et : t1 ≡ t2)
                                (evφ : extract-bprop φ [ γ , t1 ]) →
                                Inverse.from (extract-prop-iso {φ = φ} [ γ , t2 ]) (subst (λ z → extract-bprop φ [ γ , z ]) et evφ)
                                  ≡
                                ⟦ φ ⟧bprop M.⟪ tt , M.to-Σ-ty-eq ⟦ T ⟧ty (M.ctx-id ⟦ Γ ⟧ctx)
                                                                         (trans (sym (M.ty-comp ⟦ T ⟧ty)) (
                                                                           trans (cong (⟦ T ⟧ty M.⟪ tt , _ ⟫_ ∘ Inverse.from (extract-ty-iso {T})) et) (
                                                                           M.strong-ty-id ⟦ T ⟧ty)))
                                           ⟫
                                  Inverse.from (extract-prop-iso {φ = φ} [ γ , t1 ]) evφ
  extract-prop-iso-from-subst {φ = φ} refl evφ = sym (M.strong-ty-id ⟦ φ ⟧bprop)

  instance
    ∀-extractable : {T : Ty ★} → {{_ : ExtractableTy T}} →
                    {x : Name}
                    {φ : bProp (Γ ,, 𝟙 ∣ x ∈ T)} → {{ExtractableProp φ}} →
                    ExtractableProp (∀[ 𝟙 ∣ x ∈ T ] φ)
    ExtractableProp.AgdaProp (∀-extractable {T} {_} {φ}) γ = (t : extract-ty T) → extract-bprop φ [ γ , t ]
    ExtractableProp.extract-prop-iso (∀-extractable {T} {_} {φ}) γ = mk↔ₛ′
      (λ psh-f t → Inverse.to (extract-prop-iso {φ = φ} _) (psh-f Π.$⟨ tt , M.ctx-id ⟦ Γ ⟧ctx ⟩ _))
      (λ f → to-★-Π-pshfun (λ t →
        ⟦ φ ⟧bprop M.⟪ tt , M.to-Σ-ty-eq ⟦ T ⟧ty (M.ctx-id ⟦ Γ ⟧ctx) (trans (sym (M.ty-comp ⟦ T ⟧ty)) (
                                                                     trans (M.strong-ty-id ⟦ T ⟧ty) (
                                                                     Inverse.strictlyInverseʳ (extract-ty-iso {T}) t)))
                   ⟫ (
          Inverse.from (extract-prop-iso {φ = φ} [ γ , _ ]) (
          f (Inverse.to (extract-ty-iso {T}) t)))))
      (λ f → funext (λ t →
        trans (cong (Inverse.to (extract-prop-iso {φ = φ} _) ∘ (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_) ∘ (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_) ∘ Inverse.from (extract-prop-iso {φ = φ} _))
                    (sym (dcong f (sym (trans (cong (Inverse.to (extract-ty-iso {T})) (M.strong-ty-id ⟦ T ⟧ty))
                                              (Inverse.strictlyInverseˡ (extract-ty-iso {T}) t)))))) (
        trans (cong (Inverse.to (extract-prop-iso {φ = φ} _) ∘ (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_) ∘ (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_))
                    (extract-prop-iso-from-subst (sym (trans (cong (Inverse.to (extract-ty-iso {T})) (M.strong-ty-id ⟦ T ⟧ty))
                                                             (Inverse.strictlyInverseˡ (extract-ty-iso {T}) t)))
                                                 (f t))) (
        trans (cong (Inverse.to (extract-prop-iso {φ = φ} _)) (
                    trans (sym (M.ty-comp ⟦ φ ⟧bprop)) (
                    trans (sym (M.ty-comp ⟦ φ ⟧bprop)) (
                    M.strong-ty-id ⟦ φ ⟧bprop)))) (
        Inverse.strictlyInverseˡ (extract-prop-iso {φ = φ} [ γ , t ]) (f t))))))
      (λ psh-f → Π.to-pshfun-eq (λ _ eγ t →
        trans (sym (M.ty-comp ⟦ φ ⟧bprop)) (
        trans (cong (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_) (
          trans (Inverse.strictlyInverseʳ (extract-prop-iso {φ = φ} _) _) (
          trans (sym (Π.$-cong psh-f (sym (Inverse.strictlyInverseʳ (extract-ty-iso {T}) _)))) (
          trans (cong (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_) (Π.$-hom-cong psh-f refl)) (
          cong (⟦ φ ⟧bprop M.⟪ tt , _ ⟫_) (Π.naturality psh-f)))))) (
        trans (sym (trans (M.ty-comp ⟦ φ ⟧bprop) (M.ty-comp ⟦ φ ⟧bprop))) (
        M.strong-ty-id ⟦ φ ⟧bprop)))))

  mod𝟙-prop-extractable : {φ : bProp (Γ ,lock⟨ 𝟙 ⟩)} → {{_ : ExtractableProp φ}} →
                          ExtractableProp ⟨ 𝟙 ∣ φ ⟩
  ExtractableProp.AgdaProp (mod𝟙-prop-extractable {φ}) = extract-bprop φ
  ExtractableProp.extract-prop-iso (mod𝟙-prop-extractable {φ}) = extract-prop-iso {φ = φ}

open Instances public
