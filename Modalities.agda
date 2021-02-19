--------------------------------------------------
-- Definition of a modality
--------------------------------------------------

module Modalities where

open import Level

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Types.Discrete

private
  variable
    ℓc ℓc' ℓt ℓt' : Level


-- A modality is defined as a dependent right adjoint.
record Modality (C D : Category) : Setω where
  field
    ctx-op : CtxOp D C
    {{ctx-op-functor}} : IsCtxFunctor ctx-op

    mod : {Γ : Ctx D ℓc} → Ty (ctx-op Γ) ℓt → Ty Γ ℓt
    mod-cong : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} {S : Ty (ctx-op Γ) ℓt'} →
               T ≅ᵗʸ S → mod T ≅ᵗʸ mod S
    mod-natural : {Δ : Ctx D ℓc} {Γ : Ctx D ℓc'} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ) ℓt} →
                  mod T [ σ ] ≅ᵗʸ mod (T [ ctx-map σ ])

    mod-intro : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} → Tm (ctx-op Γ) T → Tm Γ (mod T)
    mod-intro-cong : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} {t t' : Tm (ctx-op Γ) T} →
                     t ≅ᵗᵐ t' → mod-intro t ≅ᵗᵐ mod-intro t'
    mod-intro-natural : {Δ : Ctx D ℓc} {Γ : Ctx D ℓc'} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ) ℓt} (t : Tm (ctx-op Γ) T) →
                        mod-intro t [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ ctx-map σ ]')

    mod-elim : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} → Tm Γ (mod T) → Tm (ctx-op Γ) T
    mod-elim-cong : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} {t t' : Tm Γ (mod T)} →
                    t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
    -- Naturality of mod-elim can in fact be proved from mod-intro-natural and the β and η laws.
    -- It is, however, often easier to prove it directly.
    mod-elim-natural : {Δ : Ctx D ℓc} {Γ : Ctx D ℓc'} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ) ℓt} (t : Tm Γ (mod T)) →
                       mod-elim t [ ctx-map σ ]' ≅ᵗᵐ mod-elim (ι⁻¹[ mod-natural σ ] (t [ σ ]'))

    mod-β : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} (t : Tm (ctx-op Γ) T) →
            mod-elim (mod-intro t) ≅ᵗᵐ t
    mod-η : {Γ : Ctx D ℓc} {T : Ty (ctx-op Γ) ℓt} (t : Tm Γ (mod T)) →
            mod-intro (mod-elim t) ≅ᵗᵐ t


module _ {C}{D} (μ : Modality C D) {Γ : Ctx D ℓc} where

  open Modality μ

  module _ {T : Ty (ctx-op Γ) ℓt} {S : Ty (ctx-op Γ) ℓt'} where

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
    from-mod-⊠ p = pair (mod-intro (fst (mod-elim p))) (mod-intro (snd (mod-elim p)))

    to-mod-⊠ : Tm Γ (mod T ⊠ mod S) → Tm Γ (mod (T ⊠ S))
    to-mod-⊠ p = mod-intro (pair (mod-elim (fst p)) (mod-elim (snd p)))

    from-to-mod-⊠ : (p : Tm Γ (mod T ⊠ mod S)) → from-mod-⊠ (to-mod-⊠ p) ≅ᵗᵐ p
    from-to-mod-⊠ p = let p' = pair (mod-elim (fst p)) (mod-elim (snd p)) in
      begin
        pair (mod-intro (fst (mod-elim (mod-intro p'))))
             (mod-intro (snd (mod-elim (mod-intro p'))))
      ≅⟨ pair-cong (mod-intro-cong (fst-cong (mod-β p')))
                   (mod-intro-cong (snd-cong (mod-β p'))) ⟩
        pair (mod-intro (fst p'))
             (mod-intro (snd p'))
      ≅⟨ pair-cong (mod-intro-cong (β-⊠-fst _ (mod-elim (snd p))))
                   (mod-intro-cong (β-⊠-snd (mod-elim (fst p)) _)) ⟩
        pair (mod-intro (mod-elim (fst p)))
             (mod-intro (mod-elim (snd p)))
      ≅⟨ pair-cong (mod-η (fst p)) (mod-η (snd p)) ⟩
        pair (fst p)
             (snd p)
      ≅˘⟨ η-⊠ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

    to-from-mod-⊠ : (p : Tm Γ (mod (T ⊠ S))) → to-mod-⊠ (from-mod-⊠ p) ≅ᵗᵐ p
    to-from-mod-⊠ p =
      let t = mod-intro (fst (mod-elim p))
          s = mod-intro (snd (mod-elim p))
      in begin
        mod-intro (pair (mod-elim (fst (pair t s)))
                        (mod-elim (snd (pair t s))))
      ≅⟨ mod-intro-cong (pair-cong (mod-elim-cong (β-⊠-fst t s))
                                   (mod-elim-cong (β-⊠-snd t s))) ⟩
        mod-intro (pair (mod-elim t)
                        (mod-elim s))
      ≅⟨ mod-intro-cong (pair-cong (mod-β _) (mod-β _)) ⟩
        mod-intro (pair (fst (mod-elim p))
                        (snd (mod-elim p)))
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
    ≅⟨ mod-intro-cong (η-unit' (mod-elim t)) ⟩
      mod-intro tt' ∎
    where open ≅ᵗᵐ-Reasoning

