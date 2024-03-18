module Experimental.LogicalFramework.Instances.GuardedRecursion.Soundness where

open import Data.String

open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.bPropExtension
open import Experimental.LogicalFramework.bProp guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Context guarded-mstt guarded-bp-ext guarded-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.Soundness guarded-mstt guarded-bp-ext guarded-bp-ext-sem
  using (Evidence)

open import Experimental.LogicalFramework.Postulates guarded-mstt guarded-bp-ext guarded-bp-ext-sem

import Model.CwF-Structure as M
import Model.DRA as M
import Applications.GuardedRecursion.Model.Streams.Guarded as M
import Applications.GuardedRecursion.Model.Modalities as M
import Applications.GuardedRecursion.Model.Modalities.Later.Closed as M
import Applications.GuardedRecursion.Model.Modalities.Later as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M


gstream-β-head-sound : (Ξ : ProofCtx ω)
                       {A : Ty ★}
                       (a : Tm (to-ctx Ξ ,lock⟨ constantly ⟩) A) (s : Tm (to-ctx Ξ ,lock⟨ later ⟩) (GStream A)) →
                       Evidence Ξ (g-head (g-cons a s) ≡ᵇ mod⟨ constantly ⟩ a)
gstream-β-head-sound Ξ a s =
  M.≅ᵗᵐ-to-Id (M.gstream-β-head _ _) M.[ _ ]'

gstream-β-tail-sound : (Ξ : ProofCtx ω)
                       {A : Ty ★}
                       (a : Tm (to-ctx Ξ ,lock⟨ constantly ⟩) A) (s : Tm (to-ctx Ξ ,lock⟨ later ⟩) (GStream A)) →
                       Evidence Ξ (g-tail (g-cons a s) ≡ᵇ mod⟨ later ⟩ s)
gstream-β-tail-sound Ξ a s =
  M.≅ᵗᵐ-to-Id (M.transᵗᵐ (M.ι⁻¹-cong (M.gstream-β-tail _ _)) M.ι-symˡ) M.[ _ ]'

tmlöb-β-sound : (Ξ : ProofCtx ω) {T : Ty ω} (x : String) (t : Tm (to-ctx Ξ ,, later ∣ x ∈ T) T) →
                Evidence Ξ (löb[later∣ x ∈ T ] t ≡ᵇ t [ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ]tmˢ)
tmlöb-β-sound Ξ {T = T} x t = M.≅ᵗᵐ-to-Id proof M.[ _ ]'
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
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (M.next-ι⁻¹ _)) ⟩
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ((M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm)
                                                  M.[ ty-closed-natural T ∣ M.from-earlier ⟦ to-ctx Ξ ⟧ctx ]cl)
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (M.next-cong (M.cl-tm-subst-cong-subst (ty-closed-natural T)
         (M.transˢ (M.⊚-congʳ (M.id-subst-unitˡ _)) (M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _)))))) ⟨
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ((M.löb-cl (ty-closed-natural T) ⟦ t ⟧tm)
                                                  M.[ ty-closed-natural T ∣ ⟦ keyʳ {Γ = to-ctx Ξ} (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ⟧ren ]cl)
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M./cl-cong (ty-closed-natural ⟨ later ∣ T ⟩) (M.next-cong
         (rename-tm-sound (löb[later∣ x ∈ T ] t) (keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr)))) ⟨
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.next ⟦ (löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ ⟧tm
                                          M./cl⟨ ty-closed-natural ⟨ later ∣ T ⟩ ⟩ ]cl
      ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (/cl-sound ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) x) ⟨
        ⟦ t ⟧tm M.[ ty-closed-natural T ∣ ⟦ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ⟧sub
                  ]cl
      ≅⟨ tm-sub-sound t (((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x) ⟩
        ⟦ t [ ((löb[later∣ x ∈ T ] t) [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]tmʳ) / x ]tmˢ ⟧tm ∎

pf-löb-sound : (Ξ : ProofCtx ω) (φ : bProp (to-ctx Ξ)) (x : String) →
               Evidence (Ξ ,,ᵇ later ∣ x ∈ φ [ keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr ]bpropʳ) φ →
               Evidence Ξ φ
pf-löb-sound Ξ φ _ p = M.löb' _ (
  M.ι⁻¹[ M.ty-subst-cong-subst-2-2 _ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.,,-map-π _))) ] (
  M.ιc⁻¹[ M.,,-cong (
    M.transᵗʸ (M.▻-natural _) (M.▻-cong (
    M.transᵗʸ (M.ty-subst-cong-ty _ (
      M.transᵗʸ (rename-bprop-sound φ (keyʳ (lock⟨ later ⟩, ◇) ◇ 𝟙≤ltr))
                (M.ty-subst-cong-subst (M.transˢ (M.⊚-congʳ (M.id-subst-unitˡ _)) (M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _))) _)))
    (M.ty-subst-cong-subst-2-2 _ (M.from-earlier-natural _)))))
        ]'
  p))
