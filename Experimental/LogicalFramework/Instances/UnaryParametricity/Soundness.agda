module Experimental.LogicalFramework.Instances.UnaryParametricity.Soundness where

open import Data.Product hiding (Σ)
open import Data.Unit

import Applications.UnaryParametricity.Model as M

open import Experimental.LogicalFramework.Instances.UnaryParametricity.MSTT
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.bPropExtension
open import Experimental.LogicalFramework.MSTT.Soundness.Substitution unary-param-mt unary-param-ty-ext unary-param-tm-ext unary-param-tm-ext-sem
open import Experimental.LogicalFramework.bProp unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Context unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
open import Experimental.LogicalFramework.Proof.Checker.ResultType unary-param-mstt unary-param-bp-ext unary-param-bp-ext-sem
  using (Evidence)

import Model.BaseCategory as M
import Model.CwF-Structure as M
import Model.DRA as M
import Model.Type.Function as M
import Experimental.DependentTypes.Model.Function as Π

private variable
  Γ : Ctx ★


private
  bPred : (A : Ty ↑) → Tm Γ ⟨ forget ∣ A ⟩ → bProp Γ
  bPred A t = ext (bPred-code A) _ (t , _) tt tt


module _ (Ξ : ProofCtx ★) where
  param-sound : (A : Ty ↑) (φ : bProp (to-ctx Ξ)) →
                ⟦ φ ⟧bprop M.≅ᵗʸ ⟦_⟧bprop {Γ = to-ctx Ξ} (∀[ Σ ∣ "a" ∈ A ] bPred A (mod⟨ forget ⟩ var "a" π-cell)) →
                Evidence Ξ φ
  param-sound A φ eφ = (M.ι[ eφ ]
    (M.ι[ Π.Pi-cong-cod (M.semPred-cong _ (
            M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural ⟨ forget ∣ A ⟩) _)
                      (M.forget-intro-cong (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural A) (M.id-subst-unitʳ _)))))
        ] M.param-sem (ty-closed-natural A))
    ) M.[ _ ]'

  extent-from-sound : (A B : Ty ↑) (φ : bProp (to-ctx Ξ)) (f : Tm (to-ctx Ξ) ⟨ forget ∣ A ⇛ B ⟩) →
                      Evidence Ξ (bPred (A ⇛ B) f) →
                      ⟦ φ ⟧bprop M.≅ᵗʸ ⟦_⟧bprop {Γ = to-ctx Ξ}
                        (∀[ forget ∣ "a" ∈ A ] bPred A (mod⟨ forget ⟩ svar "a")
                           ⊃ bPred B (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ in' mod⟨ forget ⟩ (svar "f" ∙ svar "a")))
                      →
                      Evidence Ξ φ
  extent-from-sound A B φ f pf eφ =
    M.ι[ M.ty-subst-cong-ty _ eφ ] (
    M.ι[ M.transᵗʸ (Π.Pi-natural-closed-dom (ty-closed-natural ⟨ forget ∣ A ⟩) _) (Π.Pi-cong-cod (
         M.transᵗʸ (M.⇛-natural _) (M.⇛-cong
           (M.transᵗʸ (M.semPred-natural _ _ _) (M.semPred-cong _ (
             M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ forget ∣ A ⟩) (
               M.transᵗᵐ (M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural ⟨ forget ∣ A ⟩) _) (
                 M.forget-intro-cong (M.transᵗᵐ (M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural A) _)
                   (M.cl-tm-subst-id (ty-closed-natural A) _)) (M.cl-tm-subst-id (ty-closed-natural A) _)))) (M.forget-η _))) (
             M.lift-cl-ξcl (ty-closed-natural ⟨ forget ∣ A ⟩)))))
           (M.transᵗʸ (M.semPred-natural _ _ _) (M.semPred-cong _ (
             M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ forget ∣ B ⟩) (M.cl-tm-subst-id (ty-closed-natural ⟨ forget ∣ B ⟩) _)) (
             M.transᵗᵐ (M.dra-let-natural M.𝟙 M.forget-dra (ty-closed-natural (A ⇛ B)) (ty-closed-natural ⟨ forget ∣ B ⟩) _) (
             M.transᵗᵐ (M.dra-let-cong M.𝟙 M.forget-dra (ty-closed-natural (A ⇛ B)) (ty-closed-natural ⟨ forget ∣ B ⟩)
               (M.transᵗᵐ
                 (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) (
                   M.transᵗᵐ (M.symᵗᵐ (tm-ren-sound f ((idʳ ⊚aʳ πᵃʳ) ⊚aʳ keyᵃʳ (lock⟨ 𝟙 ⟩, ◇) ◇ id-cell))) (
                   M.cl-tm-subst-cong-subst (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) (
                     M.transˢ (M.⊚-congʳ (record { eq = λ _ → refl })) (M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _))))))
                 (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) (M.lift-cl-subst-π-commute (ty-closed-natural ⟨ forget ∣ A ⟩))))
               (M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ forget ∣ B ⟩) (
                  M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural ⟨ forget ∣ B ⟩) (M.transˢ (M.,,-map-cong (lemma (ty-closed-natural (A ⇛ B)))) M.,,-map-id)) (
                  M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural ⟨ forget ∣ B ⟩) _) (M.forget-intro-cong (M.app-cong (
                  M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural (A ⇛ B)) _) (M.cl-tm-subst-id (ty-closed-natural (A ⇛ B)) _)) (
                  M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural A) _) (
                  M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural A) _) (
                  M.cl-tm-subst-cong-tm (ty-closed-natural A) (M.cl-tm-subst-id (ty-closed-natural A) _))))))))) (
                M.transᵗᵐ (M.dra-intro-cl-natural M.forget-dra (ty-closed-natural B) _) (M.forget-intro-cong (
                M.transᵗᵐ (M.app-cl-natural (ty-closed-natural A) (ty-closed-natural B)) (M.app-cong (
                M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.fun-closed-congᶜⁿ (M.symᶜⁿ (M.𝟙-preserves-cl (ty-closed-natural A))) (M.reflᶜⁿ (ty-closed-natural B)))) (
                M.transᵗᵐ (M.dra-elim-cl-natural M.forget-dra (ty-closed-natural (A ⇛ B)) _) (M.forget-elim-cong (
                M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) (M.lift-cl-subst-cong-cl (M.𝟙-preserves-cl (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩)))) (
                M.lift-cl-ξcl (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩)))))) (
                M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural A) (M.lock-fmap-cong-2-2 M.forget-dra (
                                                        M.lift-cl-subst-π-commute (ty-closed-natural ⟨ 𝟙 ∣ ⟨ forget ∣ A ⇛ B ⟩ ⟩)))) (
                M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural A) (
                   M.transᵗᵐ (M.dra-elim-cl-natural M.forget-dra (ty-closed-natural A) _) (
                   M.forget-elim-cong (M.lift-cl-ξcl (ty-closed-natural ⟨ forget ∣ A ⟩))))) (
                M.dra-elim-cl-natural M.forget-dra (ty-closed-natural A) _))))))))) (
             M.transᵗᵐ (M.dra-intro-cl-natural M.forget-dra (ty-closed-natural B) _) (M.forget-intro-cong (
             M.transᵗᵐ (M.app-cl-natural (ty-closed-natural A) (ty-closed-natural B)) (M.app-cong (
             M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.fun-closed-congᶜⁿ (M.symᶜⁿ (M.𝟙-preserves-cl (ty-closed-natural A))) (M.reflᶜⁿ (ty-closed-natural B)))) (
             M.transᵗᵐ (M.dra-elim-cl-natural M.forget-dra (ty-closed-natural (A ⇛ B)) _) (M.forget-elim-cong (
             M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) (M./cl-cong-cl (M.𝟙-preserves-cl (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩)))) (
             M.transᵗᵐ (M.,cl-β2 (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) _ _) (
             M.cl-tm-subst-cong-cl (M.dra-closed-congᶜⁿ M.forget-dra (M.fun-closed-congᶜⁿ (M.𝟙-preserves-cl (ty-closed-natural A)) (M.reflᶜⁿ (ty-closed-natural B)))))))))) (
             M.transᵗᵐ (M.dra-elim-cl-natural M.forget-dra (ty-closed-natural A) _) (
             M.forget-elim-cong (M.cl-tm-subst-cong-subst-2-0 (ty-closed-natural ⟨ forget ∣ A ⟩) (M.,cl-β1 (ty-closed-natural ⟨ 𝟙 ∣ ⟨ forget ∣ A ⇛ B ⟩ ⟩) _ _))))))))))))))))
       ]
    M.extent-from-sem (ty-closed-natural A) (ty-closed-natural B) (⟦ f ⟧tm M.[ ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩ ∣ to-ctx-subst Ξ ]cl) (
      M.ι⁻¹[ M.transᵗʸ (M.semPred-natural _ _ _) (
             M.transᵗʸ (M.semPred-congᶜⁿ (M.fun-closed-congᶜⁿ (M.𝟙-preserves-cl (ty-closed-natural A)) (M.reflᶜⁿ (ty-closed-natural B))) _) (
             M.semPred-cong (M.fun-closed (ty-closed-natural A) (ty-closed-natural B)) (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ forget ∣ A ⇛ B ⟩) (
                            M.cl-tm-subst-id (M.dra-closed M.forget-dra (M.fun-closed (M.dra-closed M.𝟙 (ty-closed-natural A)) (ty-closed-natural B))) _))))
           ] pf))
    where
      lemma : {C D : M.BaseCategory} {μ : M.DRA C D} →
              {T : M.ClosedTy C} (clT : M.IsClosedNatural T) →
              {Γ : M.Ctx D} →
              M.to (M.eq-dra-ty-closed (M.symᵈ (M.𝟙-unitˡ μ)) clT) M.≅ⁿ M.id-trans {Γ = Γ} M.⟨ μ ∣ T ⟩
      lemma {μ = μ} {T} clT =
        M.transⁿ (M.⊙-congˡ (M.⊙-congʳ M.coe-trans-𝟙-unitˡ)) (
        M.transⁿ (M.transⁿ (M.⊙-congˡ (M.symⁿ (M.dra-map-⊙ μ))) (M.symⁿ (M.dra-map-⊙ μ))) (
        M.transⁿ (M.dra-map-cong μ (M.⊙-congʳ (M.to-eq (M.closed-id clT)))) (
        M.transⁿ (M.dra-map-cong μ (record { eq = λ _ → M.strong-ty-id T })) (
        M.dra-map-id μ))))
