--------------------------------------------------
-- Definition of a modality
--------------------------------------------------

module Modalities where

open import Categories
open import CwF-Structure
open import Types.Functions
open import Types.Products
open import Types.Discrete
open import Reflection.SubstitutionSequence

private
  variable
    C D E : Category

infix 1 _≅ᵐ_
infixl 20 _ⓜ_


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
    mod-intro-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ)} (t : Tm (ctx-op Γ) T) →
                        (mod-intro t) [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ ctx-map σ ]')
    mod-intro-ι : {Γ : Ctx D} {T S : Ty (ctx-op Γ)} (T=S : T ≅ᵗʸ S) (t : Tm (ctx-op Γ) S) →
                  ι[ mod-cong T=S ] mod-intro t ≅ᵗᵐ mod-intro (ι[ T=S ] t)

    mod-elim : {Γ : Ctx D} {T : Ty (ctx-op Γ)} → Tm Γ (mod T) → Tm (ctx-op Γ) T
    mod-elim-cong : {Γ : Ctx D} {T : Ty (ctx-op Γ)} {t t' : Tm Γ (mod T)} →
                    t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
    -- Naturality of mod-elim and the fact that it commutes with ι can be proved
    -- from mod-intro-natural, mod-intro-ι  and the β and η laws (see below).

    mod-β : {Γ : Ctx D} {T : Ty (ctx-op Γ)} (t : Tm (ctx-op Γ) T) →
            mod-elim (mod-intro t) ≅ᵗᵐ t
    mod-η : {Γ : Ctx D} {T : Ty (ctx-op Γ)} (t : Tm Γ (mod T)) →
            mod-intro (mod-elim t) ≅ᵗᵐ t

  mod-elim-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (ctx-op Γ)} (t : Tm Γ (mod T)) →
                     (mod-elim t) [ ctx-map σ ]' ≅ᵗᵐ mod-elim (ι⁻¹[ mod-natural σ ] (t [ σ ]'))
  mod-elim-natural σ t = begin
    (mod-elim t) [ ctx-map σ ]'
      ≅˘⟨ mod-β _ ⟩
    mod-elim (mod-intro ((mod-elim t) [ ctx-map σ ]'))
      ≅˘⟨ mod-elim-cong (ι-symˡ (mod-natural σ) _) ⟩
    mod-elim (ι⁻¹[ mod-natural σ ] (ι[ mod-natural σ ] (mod-intro ((mod-elim t) [ ctx-map σ ]'))))
      ≅˘⟨ mod-elim-cong (ι⁻¹-cong (mod-natural σ) (mod-intro-natural σ (mod-elim t))) ⟩
    mod-elim (ι⁻¹[ mod-natural σ ] (mod-intro (mod-elim t) [ σ ]'))
      ≅⟨ mod-elim-cong (ι⁻¹-cong (mod-natural σ) (tm-subst-cong-tm σ (mod-η t))) ⟩
    mod-elim (ι⁻¹[ mod-natural σ ] (t [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning
  mod-elim-ι : {Γ : Ctx D} {T S : Ty (ctx-op Γ)} (T=S : T ≅ᵗʸ S) (t : Tm Γ (mod S)) →
               ι[ T=S ] mod-elim t ≅ᵗᵐ mod-elim (ι[ mod-cong T=S ] t)
  mod-elim-ι {T = T} {S = S} T=S t = begin
    ι[ T=S ] mod-elim t
      ≅˘⟨ mod-β _ ⟩
    mod-elim (mod-intro (ι[ T=S ] mod-elim t))
      ≅˘⟨ mod-elim-cong (mod-intro-ι _ _) ⟩
    mod-elim (ι[ mod-cong T=S ] mod-intro (mod-elim t))
      ≅⟨ mod-elim-cong (ι-cong (mod-cong T=S) (mod-η t)) ⟩
    mod-elim (ι[ mod-cong T=S ] t) ∎
    where open ≅ᵗᵐ-Reasoning



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

open Modality

-- The unit modality
𝟙 : {C : Category} → Modality C C
ctx-op 𝟙 Γ = Γ
ctx-op-functor 𝟙 = id-ctx-functor
mod 𝟙 T = T
mod-cong 𝟙 T=S = T=S
mod-natural 𝟙 σ = ≅ᵗʸ-refl
mod-intro 𝟙 t = t
mod-intro-cong 𝟙 t=t' = t=t'
mod-intro-natural 𝟙 σ t = ≅ᵗᵐ-sym (ι-refl (t [ σ ]'))
mod-intro-ι 𝟙 T=S t = ≅ᵗᵐ-refl
mod-elim 𝟙 t = t
mod-elim-cong 𝟙 t=t' = t=t'
mod-β 𝟙 t = ≅ᵗᵐ-refl
mod-η 𝟙 t = ≅ᵗᵐ-refl

-- Composition of modalities
_ⓜ_ : {C1 C2 C3 : Category} → Modality C2 C3 → Modality C1 C2 → Modality C1 C3
ctx-op (μ ⓜ ρ) Γ = ctx-op ρ (ctx-op μ Γ)
ctx-op-functor (μ ⓜ ρ) = ctx-op-functor ρ ⓕ ctx-op-functor μ
mod (μ ⓜ ρ) T = mod μ (mod ρ T)
mod-cong (μ ⓜ ρ) e = mod-cong μ (mod-cong ρ e)
mod-natural (μ ⓜ ρ) σ = ≅ᵗʸ-trans (mod-natural μ σ) (mod-cong μ (mod-natural ρ _))
mod-intro (μ ⓜ ρ) t = mod-intro μ (mod-intro ρ t)
mod-intro-cong (μ ⓜ ρ) e = mod-intro-cong μ (mod-intro-cong ρ e)
mod-intro-natural (μ ⓜ ρ) σ t = begin
  (mod-intro μ (mod-intro ρ t)) [ σ ]'
    ≅⟨ mod-intro-natural μ σ (mod-intro ρ t) ⟩
  ι[ mod-natural μ σ ] mod-intro μ ((mod-intro ρ t) [ ctx-map σ ]')
    ≅⟨ ι-cong (mod-natural μ σ) (mod-intro-cong μ (mod-intro-natural ρ (ctx-map σ) t)) ⟩
  ι[ mod-natural μ σ ] mod-intro μ (ι[ mod-natural ρ _ ] mod-intro ρ (t [ ctx-map (ctx-map {Φ = ctx-op μ} σ) ]'))
    ≅˘⟨ ι-cong (mod-natural μ σ) (mod-intro-ι μ _ _) ⟩
  ι[ mod-natural μ σ ] (ι[ mod-cong μ (mod-natural ρ _) ] mod-intro μ (mod-intro ρ (t [ ctx-map (ctx-map {Φ = ctx-op μ} σ) ]')))
    ≅˘⟨ ι-trans (mod-natural μ σ) (mod-cong μ (mod-natural ρ _)) _ ⟩
  ι[ ≅ᵗʸ-trans (mod-natural μ σ) (mod-cong μ (mod-natural ρ (ctx-map σ))) ] mod-intro μ (mod-intro ρ (t [ ctx-map (ctx-map {Φ = ctx-op μ}  σ) ]')) ∎
  where open ≅ᵗᵐ-Reasoning
mod-intro-ι (μ ⓜ ρ) T=S t = ≅ᵗᵐ-trans (mod-intro-ι μ _ _) (mod-intro-cong μ (mod-intro-ι ρ _ _))
mod-elim (μ ⓜ ρ) t = mod-elim ρ (mod-elim μ t)
mod-elim-cong (μ ⓜ ρ) e = mod-elim-cong ρ (mod-elim-cong μ e)
mod-β (μ ⓜ ρ) t = ≅ᵗᵐ-trans (mod-elim-cong ρ (mod-β μ _)) (mod-β ρ t)
mod-η (μ ⓜ ρ) t = ≅ᵗᵐ-trans (mod-intro-cong μ (mod-η ρ _)) (mod-η μ t)

-- Equivalence of modalities
record _≅ᵐ_  {C D} (μ ρ : Modality C D) : Set₁ where
  field
    eq-ctx-op : (Γ : Ctx D) → ctx-op μ Γ ≅ᶜ ctx-op ρ Γ
    eq-mod-tyʳ : {Γ : Ctx D} (T : Ty (ctx-op μ Γ)) → mod μ T ≅ᵗʸ mod ρ (T [ to (eq-ctx-op Γ) ])

    -- In the future, we will probably need an equivalence requirement for the modal term former,
    --  such as the following. For simplicity, we currently omit this.
    {-eq-mod-introʳ : {Γ : Ctx D} {T : Ty (ctx-op μ Γ)} (t : Tm (ctx-op μ Γ) T) →
                   mod-intro μ t ≅ᵗᵐ ι[ eq-mod-tyʳ T ] mod-intro ρ (t [ to (eq-ctx-op Γ) ]')-}

  eq-mod-tyˡ : {Γ : Ctx D} (T : Ty (ctx-op ρ Γ)) → mod μ (T [ from (eq-ctx-op Γ) ]) ≅ᵗʸ mod ρ T
  eq-mod-tyˡ {Γ = Γ} T = begin
    mod μ (T [ from (eq-ctx-op Γ) ])
      ≅⟨ eq-mod-tyʳ (T [ from (eq-ctx-op Γ) ]) ⟩
    mod ρ ((T [ from (eq-ctx-op Γ) ]) [ to (eq-ctx-op Γ) ])
      ≅⟨ mod-cong ρ (ty-subst-seq-cong (from (eq-ctx-op Γ) ∷ to (eq-ctx-op Γ) ◼) (id-subst _ ◼) T (isoʳ (eq-ctx-op Γ))) ⟩
    mod ρ (T [ id-subst (ctx-op ρ Γ) ])
      ≅⟨ mod-cong ρ (ty-subst-id T) ⟩
    mod ρ T ∎
    where open ≅ᵗʸ-Reasoning

  eq-mod-closed : (A : ClosedType C) {{_ : IsClosedNatural A}} {Γ : Ctx D} → mod μ {Γ} A ≅ᵗʸ mod ρ A
  eq-mod-closed A = begin
    mod μ A
      ≅⟨ eq-mod-tyʳ A ⟩
    mod ρ (A [ to (eq-ctx-op _) ])
      ≅⟨ mod-cong ρ (closed-natural (to (eq-ctx-op _))) ⟩
    mod ρ A ∎
    where open ≅ᵗʸ-Reasoning

open _≅ᵐ_ public

≅ᵐ-refl : ∀ {C D} → {μ : Modality C D} → μ ≅ᵐ μ
eq-ctx-op (≅ᵐ-refl {μ = μ}) Γ = ≅ᶜ-refl
eq-mod-tyʳ (≅ᵐ-refl {μ = μ}) T = mod-cong μ (≅ᵗʸ-sym (ty-subst-id T))

≅ᵐ-sym : ∀ {C D} {μ ρ : Modality C D} → μ ≅ᵐ ρ → ρ ≅ᵐ μ
eq-ctx-op (≅ᵐ-sym e) Γ = ≅ᶜ-sym (eq-ctx-op e Γ)
eq-mod-tyʳ (≅ᵐ-sym e) T = ≅ᵗʸ-sym (eq-mod-tyˡ e T)

≅ᵐ-trans : ∀ {C D} {μ ρ κ : Modality C D} → μ ≅ᵐ ρ → ρ ≅ᵐ κ → μ ≅ᵐ κ
eq-ctx-op (≅ᵐ-trans μ=ρ ρ=κ) Γ = ≅ᶜ-trans (eq-ctx-op μ=ρ Γ) (eq-ctx-op ρ=κ Γ)
eq-mod-tyʳ (≅ᵐ-trans {μ = μ} {ρ = ρ} {κ = κ} μ=ρ ρ=κ) {Γ = Γ} T = begin
  mod μ T
    ≅⟨ eq-mod-tyʳ μ=ρ T ⟩
  mod ρ (T [ to (eq-ctx-op μ=ρ Γ) ])
    ≅⟨ eq-mod-tyʳ ρ=κ (T [ to (eq-ctx-op μ=ρ Γ) ]) ⟩
  mod κ ((T [ to (eq-ctx-op μ=ρ Γ) ]) [ to (eq-ctx-op ρ=κ Γ) ])
    ≅⟨ mod-cong κ (ty-subst-comp T _ _) ⟩
  mod κ (T [ to (eq-ctx-op μ=ρ Γ) ⊚ to (eq-ctx-op ρ=κ Γ) ]) ∎
  where open ≅ᵗʸ-Reasoning

𝟙-identityʳ : (μ : Modality C D) → μ ⓜ 𝟙 ≅ᵐ μ
eq-ctx-op (𝟙-identityʳ μ) Γ = ≅ᶜ-refl
eq-mod-tyʳ (𝟙-identityʳ μ) T = ≅ᵗʸ-sym (mod-cong μ (ty-subst-id T))

𝟙-identityˡ : (μ : Modality C D) → 𝟙 ⓜ μ ≅ᵐ μ
eq-ctx-op (𝟙-identityˡ μ) Γ = ≅ᶜ-refl
eq-mod-tyʳ (𝟙-identityˡ μ) T = ≅ᵗʸ-sym (mod-cong μ (ty-subst-id T))

ⓜ-assoc : {C₁ C₂ C₃ C₄ : Category}
           (μ₃₄ : Modality C₃ C₄) (μ₂₃ : Modality C₂ C₃) (μ₁₂ : Modality C₁ C₂) →
           (μ₃₄ ⓜ μ₂₃) ⓜ μ₁₂ ≅ᵐ μ₃₄ ⓜ (μ₂₃ ⓜ μ₁₂)
eq-ctx-op (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) Γ = ≅ᶜ-refl
eq-mod-tyʳ (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) T = ≅ᵗʸ-sym (mod-cong μ₃₄ (mod-cong μ₂₃ (mod-cong μ₁₂ (ty-subst-id T))))

ⓜ-congˡ : (ρ : Modality D E) {μ μ' : Modality C D} → μ ≅ᵐ μ' → ρ ⓜ μ ≅ᵐ ρ ⓜ μ'
eq-ctx-op (ⓜ-congˡ ρ μ=μ') Γ = eq-ctx-op μ=μ' (ctx-op ρ Γ)
eq-mod-tyʳ (ⓜ-congˡ ρ μ=μ') T = mod-cong ρ (eq-mod-tyʳ μ=μ' T)

ⓜ-congʳ : {ρ ρ' : Modality D E} (μ : Modality C D) → ρ ≅ᵐ ρ' → ρ ⓜ μ ≅ᵐ ρ' ⓜ μ
from (eq-ctx-op (ⓜ-congʳ μ ρ=ρ') Γ) = ctx-map (from (eq-ctx-op ρ=ρ' Γ))
to (eq-ctx-op (ⓜ-congʳ μ ρ=ρ') Γ) = ctx-map (to (eq-ctx-op ρ=ρ' Γ))
isoˡ (eq-ctx-op (ⓜ-congʳ μ ρ=ρ') Γ) = ctx-map-inverse (isoˡ (eq-ctx-op ρ=ρ' Γ))
isoʳ (eq-ctx-op (ⓜ-congʳ μ ρ=ρ') Γ) = ctx-map-inverse (isoʳ (eq-ctx-op ρ=ρ' Γ))
eq-mod-tyʳ (ⓜ-congʳ {ρ = ρ} {ρ' = ρ'} μ ρ=ρ') {Γ = Γ} T = begin
  mod ρ (mod μ T)
    ≅⟨ eq-mod-tyʳ ρ=ρ' (mod μ T) ⟩
  mod ρ' ((mod μ T) [ to (eq-ctx-op ρ=ρ' Γ) ])
    ≅⟨ mod-cong ρ' (mod-natural μ (to (eq-ctx-op ρ=ρ' Γ))) ⟩
  mod ρ' (mod μ (T [ ctx-map (to (eq-ctx-op ρ=ρ' Γ)) ])) ∎
  where open ≅ᵗʸ-Reasoning

module ≅ᵐ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {μ ρ : Modality C D} → μ ≅ᵐ ρ → μ ≅ᵐ ρ
  begin_ μ=ρ = μ=ρ

  _≅⟨⟩_ : ∀ (μ {ρ} : Modality C D) → μ ≅ᵐ ρ → μ ≅ᵐ ρ
  _ ≅⟨⟩ μ=ρ = μ=ρ

  step-≅ : ∀ (μ {ρ κ} : Modality C D) → ρ ≅ᵐ κ → μ ≅ᵐ ρ → μ ≅ᵐ κ
  step-≅ _ ρ≅κ μ≅ρ = ≅ᵐ-trans μ≅ρ ρ≅κ

  step-≅˘ : ∀ (μ {ρ κ} : Modality C D) → ρ ≅ᵐ κ → ρ ≅ᵐ μ → μ ≅ᵐ κ
  step-≅˘ _ ρ≅κ ρ≅μ = ≅ᵐ-trans (≅ᵐ-sym ρ≅μ) ρ≅κ

  _∎ : ∀ (μ : Modality C D) → μ ≅ᵐ μ
  _∎ _ = ≅ᵐ-refl

  syntax step-≅  μ ρ≅κ μ≅ρ = μ ≅⟨  μ≅ρ ⟩ ρ≅κ
  syntax step-≅˘ μ ρ≅κ ρ≅μ = μ ≅˘⟨ ρ≅μ ⟩ ρ≅κ
