--------------------------------------------------
-- Definition of a modality
--------------------------------------------------

module Modalities where

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Types.Discrete


-- A modality is defined as a dependent right adjoint.
record Modality (C D : Category) : Set₁ where
  field
    ctx-op : CtxOp D C
    {{ctx-op-functor}} : IsCtxFunctor ctx-op

    mod : {Γ : Ctx D} → Ty (ctx-op Γ) → Ty Γ
    mod-cong : {Γ : Ctx D} {T S : Ty (ctx-op Γ)} →
               T ≅ᵗʸ S → mod T ≅ᵗʸ mod S
    mod-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ)} →
                  mod T [ σ ] ≅ᵗʸ mod (T [ ctx-map σ ])

    mod-intro : {Γ : Ctx D} {T : Ty (ctx-op Γ)} → Tm (ctx-op Γ) T → Tm Γ (mod T)
    mod-intro-cong : {Γ : Ctx D} {T : Ty (ctx-op Γ)} {t t' : Tm (ctx-op Γ) T} →
                     t ≅ᵗᵐ t' → mod-intro t ≅ᵗᵐ mod-intro t'
    mod-intro-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ)} (t : Tm (ctx-op Γ) T) →
                        mod-intro t [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ ctx-map σ ]')

    mod-elim : {Γ : Ctx D} {T : Ty (ctx-op Γ)} → Tm Γ (mod T) → Tm (ctx-op Γ) T
    mod-elim-cong : {Γ : Ctx D} {T : Ty (ctx-op Γ)} {t t' : Tm Γ (mod T)} →
                    t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
    -- Naturality of mod-elim can in fact be proved from mod-intro-natural and the β and η laws.
    -- It is, however, often easier to prove it directly.
    mod-elim-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ)} (t : Tm Γ (mod T)) →
                       mod-elim t [ ctx-map σ ]' ≅ᵗᵐ mod-elim (ι⁻¹[ mod-natural σ ] (t [ σ ]'))

    mod-β : {Γ : Ctx D} {T : Ty (ctx-op Γ)} (t : Tm (ctx-op Γ) T) →
            mod-elim (mod-intro t) ≅ᵗᵐ t
    mod-η : {Γ : Ctx D} {T : Ty (ctx-op Γ)} (t : Tm Γ (mod T)) →
            mod-intro (mod-elim t) ≅ᵗᵐ t


module _ {C}{D} (μ : Modality C D) {Γ : Ctx D} where

  open Modality μ

  module _ {T S : Ty (ctx-op Γ)} where

    -- A modality is a functor.
    modality-map : Tm (ctx-op Γ) (T ⇛ S) → Tm Γ (mod T) → Tm Γ (mod S)
    modality-map f t = mod-intro (f $ mod-elim t)

    infixl 12 modality-map
    syntax modality-map μ f t = f ⟨$- μ ⟩ t

    -- A modality is also an applicative functor.
    modality-⊛ : Tm Γ (mod (T ⇛ S)) → Tm Γ (mod T) → Tm Γ (mod S)
    modality-⊛ f t = mod-intro (mod-elim f $ mod-elim t)

    infixl 12 modality-⊛
    syntax modality-⊛ μ f t = f ⊛⟨ μ ⟩ t

    -- Modalities preserve products (up to isomorphism).
    from-mod-⊠ : Tm Γ (mod (T ⊠ S)) → Tm Γ (mod T ⊠ mod S)
    from-mod-⊠ p = prim-pair (mod-intro (prim-fst (mod-elim p))) (mod-intro (prim-snd (mod-elim p)))

    to-mod-⊠ : Tm Γ (mod T ⊠ mod S) → Tm Γ (mod (T ⊠ S))
    to-mod-⊠ p = mod-intro (prim-pair (mod-elim (prim-fst p)) (mod-elim (prim-snd p)))

    from-to-mod-⊠ : (p : Tm Γ (mod T ⊠ mod S)) → from-mod-⊠ (to-mod-⊠ p) ≅ᵗᵐ p
    from-to-mod-⊠ p = let p' = prim-pair (mod-elim (prim-fst p)) (mod-elim (prim-snd p)) in
      begin
        prim-pair (mod-intro (prim-fst (mod-elim (mod-intro p'))))
             (mod-intro (prim-snd (mod-elim (mod-intro p'))))
      ≅⟨ prim-pair-cong (mod-intro-cong (prim-fst-cong (mod-β p')))
                   (mod-intro-cong (prim-snd-cong (mod-β p'))) ⟩
        prim-pair (mod-intro (prim-fst p'))
             (mod-intro (prim-snd p'))
      ≅⟨ prim-pair-cong (mod-intro-cong (β-⊠-prim-fst _ (mod-elim (prim-snd p))))
                   (mod-intro-cong (β-⊠-prim-snd (mod-elim (prim-fst p)) _)) ⟩
        prim-pair (mod-intro (mod-elim (prim-fst p)))
             (mod-intro (mod-elim (prim-snd p)))
      ≅⟨ prim-pair-cong (mod-η (prim-fst p)) (mod-η (prim-snd p)) ⟩
        prim-pair (prim-fst p)
             (prim-snd p)
      ≅˘⟨ η-⊠ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

    to-from-mod-⊠ : (p : Tm Γ (mod (T ⊠ S))) → to-mod-⊠ (from-mod-⊠ p) ≅ᵗᵐ p
    to-from-mod-⊠ p =
      let t = mod-intro (prim-fst (mod-elim p))
          s = mod-intro (prim-snd (mod-elim p))
      in begin
        mod-intro (prim-pair (mod-elim (prim-fst (prim-pair t s)))
                        (mod-elim (prim-snd (prim-pair t s))))
      ≅⟨ mod-intro-cong (prim-pair-cong (mod-elim-cong (β-⊠-prim-fst t s))
                                   (mod-elim-cong (β-⊠-prim-snd t s))) ⟩
        mod-intro (prim-pair (mod-elim t)
                        (mod-elim s))
      ≅⟨ mod-intro-cong (prim-pair-cong (mod-β _) (mod-β _)) ⟩
        mod-intro (prim-pair (prim-fst (mod-elim p))
                        (prim-snd (mod-elim p)))
      ≅˘⟨ mod-intro-cong (η-⊠ (mod-elim p)) ⟩
        mod-intro (mod-elim p)
      ≅⟨ mod-η p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

  -- Modalities preserve the unit type (up to isomorphism).
  mod-unit' : Tm Γ (mod Unit')
  mod-unit' = mod-intro tt'

  mod-unit'-η : (t : Tm Γ (mod Unit')) → t ≅ᵗᵐ mod-unit'
  mod-unit'-η t =
    begin
      t
    ≅˘⟨ mod-η t ⟩
      mod-intro (mod-elim t)
    ≅⟨ mod-intro-cong (η-unit (mod-elim t)) ⟩
      mod-intro tt' ∎
    where open ≅ᵗᵐ-Reasoning
