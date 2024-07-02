--------------------------------------------------
-- Properties of type substitution with respect to natural
-- transormations between context functors
--------------------------------------------------

module Model.CwF-Structure.Type.ContextTransformation where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextFunctor
open import Model.CwF-Structure.Type

private
  variable
    C D : BaseCategory


module _ {Φ Ψ : CtxFunctor C D} (α : CtxNatTransf Φ Ψ) where
  ty-subst-ctx-transf-id : {Γ : Ctx C} {T : Ty (ctx-op Ψ Γ)} →
    transᵗʸ (ty-subst-cong-subst-2-2 T (naturality α (id-subst Γ)))
            (ty-subst-cong-ty _ (transᵗʸ (ty-subst-cong-subst (ctx-fmap-id Ψ) T) (ty-subst-id T)))
      ≅ᵉ
    transᵗʸ (ty-subst-cong-subst (ctx-fmap-id Φ) _)
            (ty-subst-id _)
  eq (from-eq (ty-subst-ctx-transf-id {T = T})) _ = ty-cong-2-1 T (hom-idˡ D)

  ty-subst-ctx-transf-⊚ : {Γ Δ Θ : Ctx C} {σ : Δ ⇒ Θ} {τ : Γ ⇒ Δ} {T : Ty (ctx-op Ψ Θ)} →
                          transᵗʸ (ty-subst-cong-ty (ctx-fmap Φ τ) (ty-subst-cong-subst-2-2 T (naturality α σ))) (
                          transᵗʸ (ty-subst-cong-subst-2-2 _ (naturality α τ)) (
                          ty-subst-cong-ty _ (transᵗʸ (ty-subst-comp T _ _) (ty-subst-cong-subst (symˢ (ctx-fmap-⊚ Ψ σ τ)) T))))
                            ≅ᵉ
                          transᵗʸ (ty-subst-comp (T [ transf-op α Θ ]) _ _) (
                          transᵗʸ (ty-subst-cong-subst (symˢ (ctx-fmap-⊚ Φ σ τ)) (T [ transf-op α Θ ])) (
                          ty-subst-cong-subst-2-2 T (naturality α (σ ⊚ τ))))
  eq (from-eq (ty-subst-ctx-transf-⊚ {T = T})) _ = trans (sym (ty-comp T)) (ty-cong-2-2 T (hom-idˡ D))

  ty-subst-ctx-transf-subst-eq : {Γ Δ : Ctx C} {σ τ : Γ ⇒ Δ} {ε : σ ≅ˢ τ} {T : Ty (ctx-op Ψ Δ)} →
                                 transᵗʸ (ty-subst-cong-subst (ctx-fmap-cong Φ ε) _) (
                                 ty-subst-cong-subst-2-2 T (naturality α τ))
                                   ≅ᵉ
                                 transᵗʸ (ty-subst-cong-subst-2-2 T (naturality α σ)) (
                                 ty-subst-cong-ty _ (ty-subst-cong-subst (ctx-fmap-cong Ψ ε) T))
  eq (from-eq (ty-subst-ctx-transf-subst-eq {T = T})) _ = ty-cong-2-2 T refl
