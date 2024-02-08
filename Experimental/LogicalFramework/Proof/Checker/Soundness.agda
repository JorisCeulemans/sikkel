open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof.Checker.Soundness
  (ℬ : BiSikkelParameter)
  where

open import Data.String

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.IdentityType.Modal as M
import Experimental.DependentTypes.Model.Constant as M
import Experimental.DependentTypes.Model.Function as M renaming (lam to dlam)
import Model.Type.Constant as M
import Model.Type.Function as M
import Model.Type.Product as M

open BiSikkelParameter ℬ
-- open import Experimental.LogicalFramework.Parameter.ProofExtension 𝒫 𝒷 ⟦𝒷⟧
-- open ProofExt 𝓅
-- open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 String

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
-- open import Experimental.LogicalFramework.Proof.Definition ℬ
-- open import Experimental.LogicalFramework.Proof.CheckingMonad
-- open import Experimental.LogicalFramework.Proof.Equality 𝒫 𝒷
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Postulates 𝒫 𝒷 ⟦𝒷⟧
-- open import Experimental.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧
-- open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n : Mode
  μ ρ : Modality m n
  x y : String
  T S : Ty m


-- A useful lemma
to-ctx-/-commute : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T))) (t : Tm (to-ctx (Ξ ,lock⟨ μ ⟩)) T) →
                   ⟦ φ [ t / x ]bprop ⟧bprop M.[ to-ctx-subst Ξ ]
                     M.≅ᵗʸ
                   (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ μ ∣ x ∈ T) ]) M.[
                    dra-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ to-ctx-subst (Ξ ,lock⟨ μ ⟩) ]cl) M./cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ ]
to-ctx-/-commute {μ = μ} {x} {T} Ξ φ t =
  M.transᵗʸ (M.symᵗʸ (M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/cl-sound t x)) ⟦ φ ⟧bprop) (bprop-sub-sound φ (t / x))))) (
  M.transᵗʸ (M.ty-subst-cong-subst-2-2 _ (M./cl-⊚ (ty-closed-natural ⟨ μ ∣ T ⟩) _ _)) (
  M.ty-subst-cong-subst (M.,cl-cong-tm (ty-closed-natural ⟨ μ ∣ T ⟩) (dra-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t ⟧tm)) _))

-- Specialisation of the previous lemma to the case μ = 𝟙
to-ctx-/-commute-𝟙 : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ 𝟙 ∣ x ∈ T))) (t : Tm (to-ctx Ξ ,lock⟨ 𝟙 ⟩) T) →
                     ⟦ φ [ t / x ]bprop ⟧bprop M.[ to-ctx-subst Ξ ]
                       M.≅ᵗʸ
                     (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ 𝟙 ∣ x ∈ T) ]) M.[
                       (⟦ t ⟧tm M.[ ty-closed-natural T ∣ to-ctx-subst Ξ ]cl) M./cl⟨ ty-closed-natural T ⟩ ]
to-ctx-/-commute-𝟙 {T = T} Ξ φ t =
  M.transᵗʸ (to-ctx-/-commute Ξ φ t) (
  M.ty-subst-cong-subst (M./cl-cong-cl (𝟙-preserves-cl (ty-closed-natural T))) _)

-- Todo: the soundness proofs for nat-induction and mod-induction can
-- probably be simplified by using the following lemma
-- to-ctx-//-commute : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ ρ ∣ y ∈ S)))
--                     (s : Tm (to-ctx Ξ ,, μ ∣ x ∈ T ,lock⟨ ρ ⟩) S) →
--                     ⟦ φ [ s // y ]bprop ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ μ ∣ x ∈ T) ]
--                       M.≅ᵗʸ
--                     (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ ρ ∣ y ∈ S) ])
--                       M.[ dra-intro ⟦ ρ ⟧mod (⟦ s ⟧tm M.[ ty-closed-natural S ∣ to-ctx-subst ((Ξ ,,ᵛ μ ∣ x ∈ T) ,lock⟨ ρ ⟩) ]cl)
--                           M.//cl⟨ ty-closed-natural ⟨ ρ ∣ S ⟩ ⟩ ]
-- to-ctx-//-commute Ξ φ s = {!!}
