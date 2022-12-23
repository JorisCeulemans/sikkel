--------------------------------------------------
-- Definition and properties of modalities
--------------------------------------------------

module Model.Modality where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.Type.Product
open import Model.Type.Constant
open import Model.CwF-Structure.Reflection.SubstitutionSequence

private
  variable
    C D E : BaseCategory

infix 1 _≅ᵐ_
infixl 20 _ⓜ_ _ⓣ-vert_ _ⓣ-hor_


--------------------------------------------------
-- Definition of a modality as a dependent right adjoint

record Modality (C D : BaseCategory) : Set₁ where
  no-eta-equality
  field
    ctx-functor : CtxFunctor D C

  lock : CtxOp D C
  lock = ctx-op ctx-functor

  lock-fmap : {Δ Γ : Ctx D} → (Δ ⇒ Γ) → (lock Δ ⇒ lock Γ)
  lock-fmap = ctx-fmap ctx-functor

  lock-fmap-cong = ctx-fmap-cong ctx-functor
  lock-fmap-id = ctx-fmap-id ctx-functor
  lock-fmap-⊚ = ctx-fmap-⊚ ctx-functor

  field
    ⟨_∣_⟩ : {Γ : Ctx D} → Ty (lock Γ) → Ty Γ
    mod-cong : {Γ : Ctx D} {T S : Ty (lock Γ)} →
               T ≅ᵗʸ S → ⟨_∣_⟩ T ≅ᵗʸ ⟨_∣_⟩ S
    mod-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} →
                  (⟨_∣_⟩ T) [ σ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap σ ])

    mod-intro : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm (lock Γ) T → Tm Γ (⟨_∣_⟩ T)
    mod-intro-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm (lock Γ) T} →
                     t ≅ᵗᵐ t' → mod-intro t ≅ᵗᵐ mod-intro t'
    mod-intro-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
                        (mod-intro t) [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ lock-fmap σ ]')
    mod-intro-ι : {Γ : Ctx D} {T S : Ty (lock Γ)} (T=S : T ≅ᵗʸ S) (t : Tm (lock Γ) S) →
                  ι[ mod-cong T=S ] mod-intro t ≅ᵗᵐ mod-intro (ι[ T=S ] t)

    mod-elim : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm Γ (⟨_∣_⟩ T) → Tm (lock Γ) T
    mod-elim-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm Γ (⟨_∣_⟩ T)} →
                    t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
    -- Naturality of mod-elim and the fact that it commutes with ι can be proved
    -- from mod-intro-natural, mod-intro-ι  and the β and η laws (see below).

    mod-β : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
            mod-elim (mod-intro t) ≅ᵗᵐ t
    mod-η : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
            mod-intro (mod-elim t) ≅ᵗᵐ t

  mod-elim-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
                     (mod-elim t) [ lock-fmap σ ]' ≅ᵗᵐ mod-elim (ι⁻¹[ mod-natural σ ] (t [ σ ]'))
  mod-elim-natural σ t = begin
    (mod-elim t) [ lock-fmap σ ]'
      ≅˘⟨ mod-β _ ⟩
    mod-elim (mod-intro ((mod-elim t) [ lock-fmap σ ]'))
      ≅˘⟨ mod-elim-cong (ι-symˡ (mod-natural σ) _) ⟩
    mod-elim (ι⁻¹[ mod-natural σ ] (ι[ mod-natural σ ] (mod-intro ((mod-elim t) [ lock-fmap σ ]'))))
      ≅˘⟨ mod-elim-cong (ι⁻¹-cong (mod-natural σ) (mod-intro-natural σ (mod-elim t))) ⟩
    mod-elim (ι⁻¹[ mod-natural σ ] (mod-intro (mod-elim t) [ σ ]'))
      ≅⟨ mod-elim-cong (ι⁻¹-cong (mod-natural σ) (tm-subst-cong-tm σ (mod-η t))) ⟩
    mod-elim (ι⁻¹[ mod-natural σ ] (t [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning

  mod-elim-ι : {Γ : Ctx D} {T S : Ty (lock Γ)} (T=S : T ≅ᵗʸ S) (t : Tm Γ (⟨_∣_⟩ S)) →
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

open Modality public

_,lock⟨_⟩ : Ctx D → Modality C D → Ctx C
Γ ,lock⟨ μ ⟩ = lock μ Γ

mod-closed : {μ : Modality C D} {T : ClosedTy C} {{_ : IsClosedNatural T}} → IsClosedNatural ⟨ μ ∣ T ⟩
IsClosedNatural.closed-natural (mod-closed {μ = μ} {T = T}) σ =
  ≅ᵗʸ-trans (mod-natural μ σ) (mod-cong μ (closed-natural {U = T} (ctx-fmap (ctx-functor μ) σ)))
eq (from-eq (IsClosedNatural.closed-id (mod-closed {μ = μ} {T = T}))) = {!!}
IsClosedNatural.closed-⊚ (mod-closed {μ = μ} {T = T}) = {!!}
IsClosedNatural.closed-subst-eq (mod-closed {μ = μ} {T = T}) = {!!}


--------------------------------------------------
-- Properties of modalities with respect to functions, products, ...

module _ (μ : Modality C D) {Γ : Ctx D} where

  module _ {T S : Ty (Γ ,lock⟨ μ ⟩)} where

    -- A modality is a functor.
    modality-map : Tm (Γ ,lock⟨ μ ⟩) (T ⇛ S) → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
    modality-map f t = mod-intro μ (f $ mod-elim μ t)

    infixl 12 modality-map
    syntax modality-map μ f t = f ⟨$- μ ⟩ t

    -- A modality is also an applicative functor.
    modality-⊛ : Tm Γ ⟨ μ ∣ T ⇛ S ⟩ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
    modality-⊛ f t = mod-intro μ (mod-elim μ f $ mod-elim μ t)

    infixl 12 modality-⊛
    syntax modality-⊛ μ f t = f ⊛⟨ μ ⟩ t

    -- Modalities preserve products (up to isomorphism).
    from-mod-⊠ : Tm Γ ⟨ μ ∣ T ⊠ S ⟩ → Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)
    from-mod-⊠ p = prim-pair (mod-intro μ (prim-fst (mod-elim μ p))) (mod-intro μ (prim-snd (mod-elim μ p)))

    to-mod-⊠ : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩) → Tm Γ ⟨ μ ∣ T ⊠ S ⟩
    to-mod-⊠ p = mod-intro μ (prim-pair (mod-elim μ (prim-fst p)) (mod-elim μ (prim-snd p)))

    from-to-mod-⊠ : (p : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)) → from-mod-⊠ (to-mod-⊠ p) ≅ᵗᵐ p
    from-to-mod-⊠ p = let p' = prim-pair (mod-elim μ (prim-fst p)) (mod-elim μ (prim-snd p)) in
      begin
        prim-pair (mod-intro μ (prim-fst (mod-elim μ (mod-intro μ p'))))
                  (mod-intro μ (prim-snd (mod-elim μ (mod-intro μ p'))))
      ≅⟨ prim-pair-cong (mod-intro-cong μ (prim-fst-cong (mod-β μ p')))
                        (mod-intro-cong μ (prim-snd-cong (mod-β μ p'))) ⟩
        prim-pair (mod-intro μ (prim-fst p'))
                  (mod-intro μ (prim-snd p'))
      ≅⟨ prim-pair-cong (mod-intro-cong μ (β-⊠-prim-fst _ (mod-elim μ (prim-snd p))))
                        (mod-intro-cong μ (β-⊠-prim-snd (mod-elim μ (prim-fst p)) _)) ⟩
        prim-pair (mod-intro μ (mod-elim μ (prim-fst p)))
                  (mod-intro μ (mod-elim μ (prim-snd p)))
      ≅⟨ prim-pair-cong (mod-η μ (prim-fst p)) (mod-η μ (prim-snd p)) ⟩
        prim-pair (prim-fst p)
                  (prim-snd p)
      ≅˘⟨ prim-η-⊠ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

    to-from-mod-⊠ : (p : Tm Γ ⟨ μ ∣ T ⊠ S ⟩) → to-mod-⊠ (from-mod-⊠ p) ≅ᵗᵐ p
    to-from-mod-⊠ p =
      let t = mod-intro μ (prim-fst (mod-elim μ p))
          s = mod-intro μ (prim-snd (mod-elim μ p))
      in begin
        mod-intro μ (prim-pair (mod-elim μ (prim-fst (prim-pair t s)))
                               (mod-elim μ (prim-snd (prim-pair t s))))
      ≅⟨ mod-intro-cong μ (prim-pair-cong (mod-elim-cong μ (β-⊠-prim-fst t s))
                                          (mod-elim-cong μ (β-⊠-prim-snd t s))) ⟩
        mod-intro μ (prim-pair (mod-elim μ t)
                               (mod-elim μ s))
      ≅⟨ mod-intro-cong μ (prim-pair-cong (mod-β μ _) (mod-β μ _)) ⟩
        mod-intro μ (prim-pair (prim-fst (mod-elim μ p))
                               (prim-snd (mod-elim μ p)))
      ≅˘⟨ mod-intro-cong μ (prim-η-⊠ (mod-elim μ p)) ⟩
        mod-intro μ (mod-elim μ p)
      ≅⟨ mod-η μ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

  -- Modalities preserve the unit type (up to isomorphism).
  mod-unit' : Tm Γ ⟨ μ ∣ Unit' ⟩
  mod-unit' = mod-intro μ tt'

  mod-unit'-η : (t : Tm Γ ⟨ μ ∣ Unit' ⟩) → t ≅ᵗᵐ mod-unit'
  mod-unit'-η t =
    begin
      t
    ≅˘⟨ mod-η μ t ⟩
      mod-intro μ (mod-elim μ t)
    ≅⟨ mod-intro-cong μ (η-unit (mod-elim μ t)) ⟩
      mod-intro μ tt' ∎
    where open ≅ᵗᵐ-Reasoning


--------------------------------------------------
-- Constructing new modalities

-- The unit modality
𝟙 : {C : BaseCategory} → Modality C C
ctx-functor 𝟙 = id-ctx-functor
⟨ 𝟙 ∣ T ⟩ = T
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
_ⓜ_ : {C1 C2 C3 : BaseCategory} → Modality C2 C3 → Modality C1 C2 → Modality C1 C3
ctx-functor (μ ⓜ ρ) = ctx-functor ρ ⓕ ctx-functor μ
⟨ μ ⓜ ρ ∣ T ⟩ = ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩
mod-cong (μ ⓜ ρ) e = mod-cong μ (mod-cong ρ e)
mod-natural (μ ⓜ ρ) σ = ≅ᵗʸ-trans (mod-natural μ σ) (mod-cong μ (mod-natural ρ _))
mod-intro (μ ⓜ ρ) t = mod-intro μ (mod-intro ρ t)
mod-intro-cong (μ ⓜ ρ) e = mod-intro-cong μ (mod-intro-cong ρ e)
mod-intro-natural (μ ⓜ ρ) σ t = begin
  (mod-intro μ (mod-intro ρ t)) [ σ ]'
    ≅⟨ mod-intro-natural μ σ (mod-intro ρ t) ⟩
  ι[ mod-natural μ σ ] mod-intro μ ((mod-intro ρ t) [ lock-fmap μ σ ]')
    ≅⟨ ι-cong (mod-natural μ σ) (mod-intro-cong μ (mod-intro-natural ρ (lock-fmap μ σ) t)) ⟩
  ι[ mod-natural μ σ ] mod-intro μ (ι[ mod-natural ρ _ ] mod-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]'))
    ≅˘⟨ ι-cong (mod-natural μ σ) (mod-intro-ι μ _ _) ⟩
  ι[ mod-natural μ σ ] (ι[ mod-cong μ (mod-natural ρ _) ] mod-intro μ (mod-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')))
    ≅˘⟨ ι-trans (mod-natural μ σ) (mod-cong μ (mod-natural ρ _)) _ ⟩
  ι[ ≅ᵗʸ-trans (mod-natural μ σ) (mod-cong μ (mod-natural ρ (lock-fmap μ σ))) ] mod-intro μ (mod-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')) ∎
  where open ≅ᵗᵐ-Reasoning
mod-intro-ι (μ ⓜ ρ) T=S t = ≅ᵗᵐ-trans (mod-intro-ι μ _ _) (mod-intro-cong μ (mod-intro-ι ρ _ _))
mod-elim (μ ⓜ ρ) t = mod-elim ρ (mod-elim μ t)
mod-elim-cong (μ ⓜ ρ) e = mod-elim-cong ρ (mod-elim-cong μ e)
mod-β (μ ⓜ ρ) t = ≅ᵗᵐ-trans (mod-elim-cong ρ (mod-β μ _)) (mod-β ρ t)
mod-η (μ ⓜ ρ) t = ≅ᵗᵐ-trans (mod-intro-cong μ (mod-η ρ _)) (mod-η μ t)


--------------------------------------------------
-- Equivalence of modalities

record _≅ᵐ_  {C D} (μ ρ : Modality C D) : Set₁ where
  field
    eq-lock : (Γ : Ctx D) → Γ ,lock⟨ μ ⟩ ≅ᶜ Γ ,lock⟨ ρ ⟩
    eq-lock-natural-to : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) →
                         to (eq-lock Γ) ⊚ lock-fmap ρ σ ≅ˢ lock-fmap μ σ ⊚ to (eq-lock Δ)
    eq-mod-tyʳ : {Γ : Ctx D} (T : Ty (Γ ,lock⟨ μ ⟩)) → ⟨ μ ∣ T ⟩ ≅ᵗʸ ⟨ ρ ∣ T [ to (eq-lock Γ) ] ⟩

    -- In the future, we will probably need an equivalence requirement for the modal term former,
    --  such as the following. For simplicity, we currently omit this.
    {-eq-mod-introʳ : {Γ : Ctx D} {T : Ty (lock μ Γ)} (t : Tm (lock μ Γ) T) →
                   mod-intro μ t ≅ᵗᵐ ι[ eq-mod-tyʳ T ] mod-intro ρ (t [ to (eq-lock Γ) ]')-}

  eq-lock-natural-from : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) →
                         from (eq-lock Γ) ⊚ lock-fmap μ σ ≅ˢ lock-fmap ρ σ ⊚ from (eq-lock Δ)
  eq-lock-natural-from {Δ} {Γ} σ = begin
    from (eq-lock Γ) ⊚ lock-fmap μ σ
      ≅˘⟨ ⊚-id-substʳ _ ⟩
    (from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ id-subst (lock μ Δ)
      ≅˘⟨ ⊚-congˡ (isoˡ (eq-lock Δ)) ⟩
    (from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ (to (eq-lock Δ) ⊚ from (eq-lock Δ))
      ≅˘⟨ ⊚-assoc ⟩
    ((from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ to (eq-lock Δ)) ⊚ from (eq-lock Δ)
      ≅⟨ ⊚-congʳ ⊚-assoc ⟩
    (from (eq-lock Γ) ⊚ (lock-fmap μ σ ⊚ to (eq-lock Δ))) ⊚ from (eq-lock Δ)
      ≅˘⟨ ⊚-congʳ (⊚-congˡ (eq-lock-natural-to σ)) ⟩
    (from (eq-lock Γ) ⊚ (to (eq-lock Γ) ⊚ lock-fmap ρ σ)) ⊚ from (eq-lock Δ)
      ≅˘⟨ ⊚-congʳ ⊚-assoc ⟩
    ((from (eq-lock Γ) ⊚ to (eq-lock Γ)) ⊚ lock-fmap ρ σ) ⊚ from (eq-lock Δ)
      ≅⟨ ⊚-congʳ (⊚-congʳ (isoʳ (eq-lock Γ))) ⟩
    (id-subst (lock ρ Γ) ⊚ lock-fmap ρ σ) ⊚ from (eq-lock Δ)
      ≅⟨ ⊚-congʳ (⊚-id-substˡ _) ⟩
    lock-fmap ρ σ ⊚ from (eq-lock Δ) ∎
    where open ≅ˢ-Reasoning

  eq-mod-tyˡ : {Γ : Ctx D} (T : Ty (lock ρ Γ)) → ⟨ μ ∣ T [ from (eq-lock Γ) ] ⟩ ≅ᵗʸ ⟨ ρ ∣ T ⟩
  eq-mod-tyˡ {Γ = Γ} T = begin
    ⟨ μ ∣ T [ from (eq-lock Γ) ] ⟩
      ≅⟨ eq-mod-tyʳ (T [ from (eq-lock Γ) ]) ⟩
    ⟨ ρ ∣ (T [ from (eq-lock Γ) ]) [ to (eq-lock Γ) ] ⟩
      ≅⟨ mod-cong ρ (ty-subst-seq-cong (from (eq-lock Γ) ∷ to (eq-lock Γ) ◼) (id-subst _ ◼) T (isoʳ (eq-lock Γ))) ⟩
    ⟨ ρ ∣ T [ id-subst (Γ ,lock⟨ ρ ⟩) ] ⟩
      ≅⟨ mod-cong ρ (ty-subst-id T) ⟩
    ⟨ ρ ∣ T ⟩ ∎
    where open ≅ᵗʸ-Reasoning

  eq-mod-closed : (A : ClosedTy C) {{_ : IsClosedNatural A}} {Γ : Ctx D} → ⟨ μ ∣ A {Γ ,lock⟨ μ ⟩} ⟩ ≅ᵗʸ ⟨ ρ ∣ A ⟩
  eq-mod-closed A = begin
    ⟨ μ ∣ A ⟩
      ≅⟨ eq-mod-tyʳ A ⟩
    ⟨ ρ ∣ A [ to (eq-lock _) ] ⟩
      ≅⟨ mod-cong ρ (closed-natural {U = A} (to (eq-lock _))) ⟩
    ⟨ ρ ∣ A ⟩ ∎
    where open ≅ᵗʸ-Reasoning

open _≅ᵐ_ public

≅ᵐ-refl : ∀ {C D} → {μ : Modality C D} → μ ≅ᵐ μ
eq-lock (≅ᵐ-refl {μ = μ}) Γ = ≅ᶜ-refl
eq-lock-natural-to (≅ᵐ-refl {μ = μ}) σ = ≅ˢ-trans (⊚-id-substˡ _) (≅ˢ-sym (⊚-id-substʳ _))
eq-mod-tyʳ (≅ᵐ-refl {μ = μ}) T = mod-cong μ (≅ᵗʸ-sym (ty-subst-id T))

≅ᵐ-sym : ∀ {C D} {μ ρ : Modality C D} → μ ≅ᵐ ρ → ρ ≅ᵐ μ
eq-lock (≅ᵐ-sym e) Γ = ≅ᶜ-sym (eq-lock e Γ)
eq-lock-natural-to (≅ᵐ-sym e) σ = eq-lock-natural-from e σ
eq-mod-tyʳ (≅ᵐ-sym e) T = ≅ᵗʸ-sym (eq-mod-tyˡ e T)

≅ᵐ-trans : ∀ {C D} {μ ρ κ : Modality C D} → μ ≅ᵐ ρ → ρ ≅ᵐ κ → μ ≅ᵐ κ
eq-lock (≅ᵐ-trans μ=ρ ρ=κ) Γ = ≅ᶜ-trans (eq-lock μ=ρ Γ) (eq-lock ρ=κ Γ)
eq-lock-natural-to (≅ᵐ-trans {μ = μ} {ρ} {κ} μ=ρ ρ=κ) σ = begin
  (to (eq-lock μ=ρ _) ⊚ to (eq-lock ρ=κ _)) ⊚ lock-fmap κ σ
    ≅⟨ ⊚-assoc ⟩
  to (eq-lock μ=ρ _) ⊚ (to (eq-lock ρ=κ _) ⊚ lock-fmap κ σ)
    ≅⟨ ⊚-congˡ (eq-lock-natural-to ρ=κ σ) ⟩
  to (eq-lock μ=ρ _) ⊚ (lock-fmap ρ σ ⊚ to (eq-lock ρ=κ _))
    ≅˘⟨ ⊚-assoc ⟩
  (to (eq-lock μ=ρ _) ⊚ lock-fmap ρ σ) ⊚ to (eq-lock ρ=κ _)
    ≅⟨ ⊚-congʳ (eq-lock-natural-to μ=ρ σ) ⟩
  (lock-fmap μ σ ⊚ to (eq-lock μ=ρ _)) ⊚ to (eq-lock ρ=κ _)
    ≅⟨ ⊚-assoc ⟩
  lock-fmap μ σ ⊚ (to (eq-lock μ=ρ _) ⊚ to (eq-lock ρ=κ _)) ∎
  where open ≅ˢ-Reasoning
eq-mod-tyʳ (≅ᵐ-trans {μ = μ} {ρ = ρ} {κ = κ} μ=ρ ρ=κ) {Γ = Γ} T = begin
  ⟨ μ ∣ T ⟩
    ≅⟨ eq-mod-tyʳ μ=ρ T ⟩
  ⟨ ρ ∣ T [ to (eq-lock μ=ρ Γ) ] ⟩
    ≅⟨ eq-mod-tyʳ ρ=κ (T [ to (eq-lock μ=ρ Γ) ]) ⟩
  ⟨ κ ∣ (T [ to (eq-lock μ=ρ Γ) ]) [ to (eq-lock ρ=κ Γ) ] ⟩
    ≅⟨ mod-cong κ (ty-subst-comp T _ _) ⟩
  ⟨ κ ∣ T [ to (eq-lock μ=ρ Γ) ⊚ to (eq-lock ρ=κ Γ) ] ⟩ ∎
  where open ≅ᵗʸ-Reasoning

𝟙-identityʳ : (μ : Modality C D) → μ ⓜ 𝟙 ≅ᵐ μ
eq-lock (𝟙-identityʳ μ) Γ = ≅ᶜ-refl
eq (eq-lock-natural-to (𝟙-identityʳ μ) σ) _ = refl
eq-mod-tyʳ (𝟙-identityʳ μ) T = ≅ᵗʸ-sym (mod-cong μ (ty-subst-id T))

𝟙-identityˡ : (μ : Modality C D) → 𝟙 ⓜ μ ≅ᵐ μ
eq-lock (𝟙-identityˡ μ) Γ = ≅ᶜ-refl
eq (eq-lock-natural-to (𝟙-identityˡ μ) σ) _ = refl
eq-mod-tyʳ (𝟙-identityˡ μ) T = ≅ᵗʸ-sym (mod-cong μ (ty-subst-id T))

ⓜ-assoc : {C₁ C₂ C₃ C₄ : BaseCategory}
           (μ₃₄ : Modality C₃ C₄) (μ₂₃ : Modality C₂ C₃) (μ₁₂ : Modality C₁ C₂) →
           (μ₃₄ ⓜ μ₂₃) ⓜ μ₁₂ ≅ᵐ μ₃₄ ⓜ (μ₂₃ ⓜ μ₁₂)
eq-lock (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) Γ = ≅ᶜ-refl
eq (eq-lock-natural-to (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) σ) _ = refl
eq-mod-tyʳ (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) T = ≅ᵗʸ-sym (mod-cong μ₃₄ (mod-cong μ₂₃ (mod-cong μ₁₂ (ty-subst-id T))))

ⓜ-congˡ : (ρ : Modality D E) {μ μ' : Modality C D} → μ ≅ᵐ μ' → ρ ⓜ μ ≅ᵐ ρ ⓜ μ'
eq-lock (ⓜ-congˡ ρ μ=μ') Γ = eq-lock μ=μ' (Γ ,lock⟨ ρ ⟩)
eq-lock-natural-to (ⓜ-congˡ ρ {μ} {μ'} μ=μ') σ = eq-lock-natural-to μ=μ' (lock-fmap ρ σ)
eq-mod-tyʳ (ⓜ-congˡ ρ μ=μ') T = mod-cong ρ (eq-mod-tyʳ μ=μ' T)

ⓜ-congʳ : {ρ ρ' : Modality D E} (μ : Modality C D) → ρ ≅ᵐ ρ' → ρ ⓜ μ ≅ᵐ ρ' ⓜ μ
from (eq-lock (ⓜ-congʳ μ ρ=ρ') Γ) = lock-fmap μ (from (eq-lock ρ=ρ' Γ))
to (eq-lock (ⓜ-congʳ μ ρ=ρ') Γ) = lock-fmap μ (to (eq-lock ρ=ρ' Γ))
isoˡ (eq-lock (ⓜ-congʳ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoˡ (eq-lock ρ=ρ' Γ))
isoʳ (eq-lock (ⓜ-congʳ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoʳ (eq-lock ρ=ρ' Γ))
eq-lock-natural-to (ⓜ-congʳ {ρ = ρ} {ρ'} μ ρ=ρ') σ = begin
  lock-fmap μ (to (eq-lock ρ=ρ' _)) ⊚ lock-fmap μ (lock-fmap ρ' σ)
    ≅˘⟨ lock-fmap-⊚ μ _ _ ⟩
  lock-fmap μ (to (eq-lock ρ=ρ' _) ⊚ lock-fmap ρ' σ)
    ≅⟨ lock-fmap-cong μ (eq-lock-natural-to ρ=ρ' σ) ⟩
  lock-fmap μ (lock-fmap ρ σ ⊚ to (eq-lock ρ=ρ' _))
    ≅⟨ lock-fmap-⊚ μ _ _ ⟩
  lock-fmap μ (lock-fmap ρ σ) ⊚ lock-fmap μ (to (eq-lock ρ=ρ' _)) ∎
  where open ≅ˢ-Reasoning
eq-mod-tyʳ (ⓜ-congʳ {ρ = ρ} {ρ' = ρ'} μ ρ=ρ') {Γ = Γ} T = begin
  ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩
    ≅⟨ eq-mod-tyʳ ρ=ρ' ⟨ μ ∣ T ⟩ ⟩
  ⟨ ρ' ∣ ⟨ μ ∣ T ⟩ [ to (eq-lock ρ=ρ' Γ) ] ⟩
    ≅⟨ mod-cong ρ' (mod-natural μ (to (eq-lock ρ=ρ' Γ))) ⟩
  ⟨ ρ' ∣ ⟨ μ ∣ T [ lock-fmap μ (to (eq-lock ρ=ρ' Γ)) ] ⟩ ⟩ ∎
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


--------------------------------------------------
-- Two-cells between modalities as natural transformations
--   between the underlying context functors

-- TwoCell is defined as a record type so that Agda can better infer the two endpoint
--   modalities, e.g. in coe-ty.
record TwoCell (μ ρ : Modality C D) : Set₁ where
  constructor two-cell
  field
    transf : CtxNatTransf (ctx-functor ρ) (ctx-functor μ)

open TwoCell public

module _ {μ ρ : Modality C D} (α : TwoCell μ ρ) where
  coe-ty : {Γ : Ctx D} → Ty (Γ ,lock⟨ μ ⟩) → Ty (Γ ,lock⟨ ρ ⟩)
  coe-ty {Γ} T = T [ transf-op (transf α) Γ ]

  coe : {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ coe-ty T ⟩
  coe t = mod-intro ρ ((mod-elim μ t) [ transf-op (transf α) _ ]')

  coe-closed : {T : ClosedTy C} {{_ : IsClosedNatural T}} {Γ : Ctx D} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
  coe-closed {T = T} t = ι⁻¹[ mod-cong ρ (closed-natural {U = T} (transf-op (transf α) _)) ] coe t


-- The identity 2-cell.
id-cell : {μ : Modality C D} → TwoCell μ μ
transf id-cell = id-ctx-transf _

-- Composition of 2-cells (both vertical and horizontal)
_ⓣ-vert_ : {μ ρ κ : Modality C D} → TwoCell μ ρ → TwoCell κ μ → TwoCell κ ρ
transf (α ⓣ-vert β) = transf β ⓝ-vert transf α

_ⓣ-hor_ : {μ μ' : Modality D E} {ρ ρ' : Modality C D} → TwoCell μ μ' → TwoCell ρ ρ' → TwoCell (μ ⓜ ρ) (μ' ⓜ ρ')
transf (α ⓣ-hor β) = transf β ⓝ-hor transf α

-- An equivalence of modalities gives rise to an invertible 2-cell.
≅ᵐ-to-2-cell : {μ ρ : Modality C D} → μ ≅ᵐ ρ → TwoCell μ ρ
transf-op (transf (≅ᵐ-to-2-cell μ=ρ)) Γ = to (eq-lock μ=ρ Γ)
naturality (transf (≅ᵐ-to-2-cell μ=ρ)) = eq-lock-natural-to μ=ρ
