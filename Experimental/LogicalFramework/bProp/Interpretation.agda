--------------------------------------------------
-- Interpretation of propositions in a presheaf model
--------------------------------------------------

open import Data.String
open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics

module Experimental.LogicalFramework.bProp.Interpretation
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 String 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 _ _)
  where

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy) using (_≅ᵗʸ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp.Named 𝒫 𝒷
open import Experimental.LogicalFramework.bProp.AlphaEquivalence 𝒫 𝒷
open import Experimental.LogicalFramework.bProp.AlphaEquivalence.bPropExtension 𝒫
open import Experimental.LogicalFramework.bProp.Interpretation.Nameless 𝒫 (erase-names-bpext 𝒷) ⟦𝒷⟧

private variable
  m : Mode
  Γ Δ : Ctx m


-- Just as with the STT interpretation, this interpretation goes via unnamed propositions.
--   This makes it nearly trivial to prove that α-equivalent propositions have the same
--   interpretation.
⟦_⟧bprop : bProp Γ → SemTy ⟦ Γ ⟧ctx
⟦ φ ⟧bprop = ⟦ erase-names-bprop φ ⟧bprop-nmls

{-
bprop-subst-sound : (φ : bProp Γ) (σ : SubstExpr Δ Γ) → ⟦ φ ⟧bprop M.[ ⟦ σ ⟧subst ] ≅ᵗʸ ⟦ φ [ σ ]bprop ⟧bprop
bprop-subst-sound ⊤ᵇ σ = M.Const-natural _ _
bprop-subst-sound ⊥ᵇ σ = M.Const-natural _ _
bprop-subst-sound (t1 ≡ᵇ t2) σ =
  M.transᵗʸ (M.Id-natural _) (M.Id-cong (closed-ty-natural _ _) (M.move-ι⁻¹-right (M.symᵗʸ (closed-ty-natural _ _)) (tm-subst-sound t1 σ))
                                                                  (M.move-ι⁻¹-right (M.symᵗʸ (closed-ty-natural _ _)) (tm-subst-sound t2 σ)))
bprop-subst-sound (φ ⊃ ψ) σ = M.transᵗʸ (M.⇛-natural _) (M.⇛-cong (bprop-subst-sound φ σ) (bprop-subst-sound ψ σ))
bprop-subst-sound (φ ∧ ψ) σ = M.transᵗʸ (M.⊠-natural _) (M.⊠-cong (bprop-subst-sound φ σ) (bprop-subst-sound ψ σ))
bprop-subst-sound (∀[ x ∈ T ] φ) σ = M.transᵗʸ (sPi-natural _) (sPi-cong₂ (bprop-subst-sound φ (σ ⊹⟨ x ⟩)))
-}
