module Experimental.LogicalFramework.Instances.GuardedRecursion.Soundness where

open import Data.String

open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.bPropExtension
open import Experimental.LogicalFramework.MSTT.Soundness.Substitution guarded-mt guarded-ty-ext guarded-tm-ext guarded-tm-ext-sem
open import Experimental.LogicalFramework.bProp guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.bProp.Soundness.Substitution guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Context guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.ResultType guarded-mstt guarded-bp-ext guarded-bp-ext-sem
  using (Evidence)

import Model.CwF-Structure as M
import Model.DRA as M
import Applications.GuardedRecursion.Model.Streams.Guarded as M
import Applications.GuardedRecursion.Model.Modalities as M
import Applications.GuardedRecursion.Model.Lob as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M


tmlöb-β-sound : (Ξ : ProofCtx ω) {T : Ty ω} (x : String) (t : Tm (to-ctx Ξ ,, later ∣ x ∈ T) T)
                (rhs : Tm (to-ctx Ξ) T) →
                ⟦ rhs ⟧tm M.≅ᵗᵐ ⟦ t [ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ]tmˢ ⟧tm →
                Evidence Ξ (löb[later∣ x ∈ T ] t ≡ᵇ rhs)
tmlöb-β-sound Ξ {T = T} x t rhs e-rhs = M.≅ᵗᵐ-to-Id (
  M.transᵗᵐ (M.transᵗᵐ (M.löb-cl-cong (ty-closed-natural T) (
    M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (M.ctx-fmap-id (M.,,-functor (ty-closed-natural (⟨ later ∣ T ⟩)))))
              (M.cl-tm-subst-id (ty-closed-natural T) _)))
  proof)
  (M.symᵗᵐ e-rhs)) M.[ _ ]'
  where
    open M.≅ᵗᵐ-Reasoning
    proof : M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm M.≅ᵗᵐ ⟦ t [ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ]tmˢ ⟧tm
    proof =
      begin
        M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm
      ≅⟨ M.löb-cl-β (ty-closed-natural T) ⟦ t ⟧tm ⟩
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next-cl (ty-closed-natural T) (M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm)
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩
                  ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T)
                                  (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (M.next-ι⁻¹ {T=T' = M.▻-cong (M.closed-natural (ty-closed-natural T) (M.from-earlier _))} _)) ⟩
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ((M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm)
                                                  M.[ ty-closed-natural T ∣ M.from-earlier ⟦ to-ctx Ξ ⟧ctx ]cl)
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (M.next-cong (M.cl-tm-subst-cong-subst (ty-closed-natural T)
         (M.transˢ (M.⊚-congʳ (M.id-subst-unitˡ _)) (M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _)))))) ⟨
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ((M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm)
                                                  M.[ ty-closed-natural T ∣ ⟦ keyʳ {Γ = to-ctx Ξ} (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ⟧ren ]cl)
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (
           M.next-cong (M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.löb-cl-cong (ty-closed-natural T) (
           M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (M.ctx-fmap-id (M.,,-functor (ty-closed-natural ⟨ later ∣ T ⟩))))
                     (M.cl-tm-subst-id (ty-closed-natural T) ⟦ t ⟧tm)))))) ⟨
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ((M.löb-cl (ty-closed-natural T) (
                                                            ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.ctx-fmap (M.,,-functor (ty-closed-natural ⟨ later ∣ T ⟩)) (M.id-subst _) ]cl))
                                                  M.[ ty-closed-natural T ∣ ⟦ keyʳ {Γ = to-ctx Ξ} (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ⟧ren ]cl)
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (M.next-cong
         (tm-ren-sound (löb[later∣ x ∈ T ] t) (keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr)))) ⟩
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ⟦ (löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ ⟧tm
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (/cl-sound ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) x) ⟨
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ⟧sub
                  ]cl
      ≅⟨ tm-sub-sound {Δ = to-ctx Ξ ,, later ∣ x ∈ T} {Γ = to-ctx Ξ} t (((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x) ⟩
        ⟦ t [ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ]tmˢ ⟧tm ∎

pf-löb-sound : (Ξ : ProofCtx ω) (φ : bProp (to-ctx Ξ)) (x : String) →
               Evidence (Ξ ,,ᵇ later ∣ x ∈ φ [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]bpropʳ) φ →
               Evidence Ξ φ
pf-löb-sound Ξ φ _ p = M.löb' _ (
  M.ι⁻¹[ M.ty-subst-cong-subst-2-2 _ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.,,-map-π _))) ] (
  M.ιc⁻¹[ M.,,-cong (
    M.transᵗʸ (M.▻-natural _) (M.▻-cong (
    M.transᵗʸ (M.ty-subst-cong-ty _ (
      M.transᵗʸ (M.symᵗʸ (bprop-ren-sound φ (keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr)))
                (M.ty-subst-cong-subst (M.transˢ (M.⊚-congʳ (M.id-subst-unitˡ _)) (M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _))) _)))
    (M.ty-subst-cong-subst-2-2 _ (M.from-earlier-natural _)))))
        ]'
  p))
