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

infix 1 _≅ᵐ_ _≅ᵗᶜ_
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

    -- The modal type former should respect type morphisms
    -- (i.e. natural transformations between presheaves). This should
    -- be handled in a coherent way, in other words we should get a
    -- functor from the category Ty (lock Γ) to the category Ty Γ.
    -- Previously, we only required equivalence preservation (i.e. of
    -- natural isomorphisms between types). The transition from
    -- equivalence to morphism is partly joint work with Youie Li.
    mod-map : {Γ : Ctx D} {T S : Ty (lock Γ)} →
              (T ↣ S) → ⟨_∣_⟩ T ↣ ⟨_∣_⟩ S
    mod-map-cong : {Γ : Ctx D} {T S : Ty (lock Γ)} {φ η : T ↣ S} → φ ≅ⁿ η →
                   mod-map φ ≅ⁿ mod-map η
    mod-map-id : {Γ : Ctx D} {T : Ty (lock Γ)} → mod-map (id-trans T) ≅ⁿ id-trans (⟨_∣_⟩ T)
    mod-map-⊙ : {Γ : Ctx D} {R T S : Ty (lock Γ)} {φ : T ↣ S} {η : R ↣ T} →
                mod-map (φ ⊙ η) ≅ⁿ mod-map φ ⊙ mod-map η

    -- We can push substitutions under the modal type former but they
    -- get locked. Again, this must happen in a coherent way (i.e. the
    -- modal type former is a pseudonatural transformation from the
    -- pseudofunctor Ty ∘ lock to Ty).
    mod-natural : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T : Ty (lock Δ)} →
                  (⟨_∣_⟩ T) [ σ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap σ ])
    mod-natural-map : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T S : Ty (lock Δ)} (η : T ↣ S) →
                      mod-map (ty-subst-map (lock-fmap σ) η) ⊙ from (mod-natural σ {T = T})
                        ≅ⁿ
                      from (mod-natural σ) ⊙ ty-subst-map σ (mod-map η)
    mod-natural-id-map : {Γ : Ctx D} {T : Ty (lock Γ)} →
                         mod-map (from (ty-subst-id T) ⊙ ty-subst-eq-subst-morph lock-fmap-id T) ⊙ from (mod-natural (id-subst Γ))
                           ≅ⁿ
                         from (ty-subst-id (⟨_∣_⟩ T))
    mod-natural-⊚-map : {Γ Δ Θ : Ctx D} (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (lock Θ)} →
                        mod-map (from (ty-subst-comp T (lock-fmap τ) (lock-fmap σ))) ⊙ from (mod-natural σ) ⊙ ty-subst-map σ (from (mod-natural τ))
                          ≅ⁿ
                        mod-map (ty-subst-eq-subst-morph (lock-fmap-⊚ τ σ) T) ⊙ from (mod-natural (τ ⊚ σ)) ⊙ from (ty-subst-comp (⟨_∣_⟩ T) τ σ)
    mod-natural-subst-eq-map : {Γ Δ : Ctx D} {σ τ : Γ ⇒ Δ} {T : Ty (lock Δ)} (ε : σ ≅ˢ τ) →
                               from (mod-natural τ) ⊙ ty-subst-eq-subst-morph ε (⟨_∣_⟩ T)
                                 ≅ⁿ
                               mod-map (ty-subst-eq-subst-morph (lock-fmap-cong ε) T) ⊙ from (mod-natural σ)

    -- Term formers coming with a modality and their laws.
    mod-intro : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm (lock Γ) T → Tm Γ (⟨_∣_⟩ T)
    mod-intro-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm (lock Γ) T} →
                     t ≅ᵗᵐ t' → mod-intro t ≅ᵗᵐ mod-intro t'
    mod-intro-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
                        (mod-intro t) [ σ ]' ≅ᵗᵐ ι[ mod-natural σ ] mod-intro (t [ lock-fmap σ ]')
    mod-intro-convert : {Γ : Ctx D} {T S : Ty (lock Γ)} {η : T ↣ S} (t : Tm (lock Γ) T) →
                        convert-term (mod-map η) (mod-intro t) ≅ᵗᵐ mod-intro (convert-term η t)

    mod-elim : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm Γ (⟨_∣_⟩ T) → Tm (lock Γ) T
    mod-elim-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm Γ (⟨_∣_⟩ T)} →
                    t ≅ᵗᵐ t' → mod-elim t ≅ᵗᵐ mod-elim t'
    -- Naturality of mod-elim and the fact that it commutes with convert-term can be proved
    -- from mod-intro-natural, mod-intro-convert and the β and η laws (see below).

    mod-β : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
            mod-elim (mod-intro t) ≅ᵗᵐ t
    mod-η : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
            mod-intro (mod-elim t) ≅ᵗᵐ t

open Modality public
_,lock⟨_⟩ : Ctx D → Modality C D → Ctx C
Γ ,lock⟨ μ ⟩ = lock μ Γ


module _ (μ : Modality C D) where
  mod-cong : {Γ : Ctx D} {T S : Ty (lock μ Γ)} →
             T ≅ᵗʸ S → ⟨ μ ∣ T ⟩ ≅ᵗʸ ⟨ μ ∣ S ⟩
  from (mod-cong e) = mod-map μ (from e)
  to (mod-cong e) = mod-map μ (to e)
  isoˡ (mod-cong e) = transⁿ (symⁿ (mod-map-⊙ μ)) (transⁿ (mod-map-cong μ (isoˡ e)) (mod-map-id μ))
  isoʳ (mod-cong e) = transⁿ (symⁿ (mod-map-⊙ μ)) (transⁿ (mod-map-cong μ (isoʳ e)) (mod-map-id μ))

  mod-cong-refl : {Γ : Ctx D} {T : Ty (lock μ Γ)} → mod-cong (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
  from-eq mod-cong-refl = mod-map-id μ

  mod-cong-sym : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {e : T ≅ᵗʸ S} → mod-cong (symᵗʸ e) ≅ᵉ symᵗʸ (mod-cong e)
  from-eq mod-cong-sym = reflⁿ

  mod-cong-trans : {Γ : Ctx D} {R T S : Ty (lock μ Γ)} {e : R ≅ᵗʸ T} {e' : T ≅ᵗʸ S} →
                   mod-cong (transᵗʸ e e') ≅ᵉ transᵗʸ (mod-cong e) (mod-cong e')
  from-eq mod-cong-trans = mod-map-⊙ μ

  mod-cong-cong : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → mod-cong e ≅ᵉ mod-cong e'
  from-eq (mod-cong-cong 𝑒) = mod-map-cong μ (from-eq 𝑒)

  mod-natural-ty-eq : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T S : Ty (lock μ Δ)} (e : T ≅ᵗʸ S) →
                      transᵗʸ (mod-natural μ σ {T = T}) (mod-cong (ty-subst-cong-ty (lock-fmap μ σ) e))
                        ≅ᵉ
                      transᵗʸ (ty-subst-cong-ty σ (mod-cong e)) (mod-natural μ σ)
  from-eq (mod-natural-ty-eq σ e) = mod-natural-map μ σ (from e)

  mod-natural-id : {Γ : Ctx D} {T : Ty (lock μ Γ)} →
                   transᵗʸ (mod-natural μ _) (mod-cong (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) T) (ty-subst-id T)))
                     ≅ᵉ
                   ty-subst-id ⟨ μ ∣ T ⟩
  from-eq mod-natural-id = mod-natural-id-map μ

  mod-natural-⊚ : {Γ Δ Θ : Ctx D} (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (lock μ Θ)} →
                  transᵗʸ (ty-subst-cong-ty σ (mod-natural μ τ)) (transᵗʸ (mod-natural μ σ) (mod-cong (ty-subst-comp T _ _)))
                    ≅ᵉ
                  transᵗʸ (ty-subst-comp ⟨ μ ∣ T ⟩ τ σ) (transᵗʸ (mod-natural μ (τ ⊚ σ)) (mod-cong (ty-subst-cong-subst (lock-fmap-⊚ μ τ σ) T)))
  from-eq (mod-natural-⊚ τ σ) = mod-natural-⊚-map μ τ σ

  mod-natural-subst-eq : {Γ Δ : Ctx D} {σ τ : Γ ⇒ Δ} {T : Ty (lock μ Δ)} (ε : σ ≅ˢ τ) →
                         transᵗʸ (ty-subst-cong-subst ε ⟨ μ ∣ T ⟩) (mod-natural μ τ)
                           ≅ᵉ
                         transᵗʸ (mod-natural μ σ) (mod-cong (ty-subst-cong-subst (lock-fmap-cong μ ε) T))
  from-eq (mod-natural-subst-eq ε) = mod-natural-subst-eq-map μ ε


  mod-intro-ι : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {T=S : T ≅ᵗʸ S} (t : Tm (lock μ Γ) S) →
                ι[ mod-cong T=S ] mod-intro μ t ≅ᵗᵐ mod-intro μ (ι[ T=S ] t)
  mod-intro-ι t = transᵗᵐ ι-convert (transᵗᵐ (mod-intro-convert μ t) (mod-intro-cong μ (symᵗᵐ ι-convert)))

  mod-elim-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock μ Γ)} (t : Tm Γ ⟨ μ ∣ T ⟩) →
                     (mod-elim μ t) [ lock-fmap μ σ ]' ≅ᵗᵐ mod-elim μ (ι⁻¹[ mod-natural μ σ ] (t [ σ ]'))
  mod-elim-natural σ t = begin
      (mod-elim μ t) [ lock-fmap μ σ ]'
    ≅˘⟨ mod-β μ _ ⟩
      mod-elim μ (mod-intro μ ((mod-elim μ t) [ lock-fmap μ σ ]'))
    ≅˘⟨ mod-elim-cong μ ι-symˡ ⟩
      mod-elim μ (ι⁻¹[ mod-natural μ σ ] (ι[ mod-natural μ σ ] (mod-intro μ ((mod-elim μ t) [ lock-fmap μ σ ]'))))
    ≅˘⟨ mod-elim-cong μ (ι⁻¹-cong (mod-intro-natural μ σ (mod-elim μ t))) ⟩
      mod-elim μ (ι⁻¹[ mod-natural μ σ ] (mod-intro μ (mod-elim μ t) [ σ ]'))
    ≅⟨ mod-elim-cong μ (ι⁻¹-cong (tm-subst-cong-tm σ (mod-η μ t))) ⟩
      mod-elim μ (ι⁻¹[ mod-natural μ σ ] (t [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning

  mod-elim-ι : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {T=S : T ≅ᵗʸ S} (t : Tm Γ ⟨ μ ∣ S ⟩) →
               ι[ T=S ] mod-elim μ t ≅ᵗᵐ mod-elim μ (ι[ mod-cong T=S ] t)
  mod-elim-ι {T = T} {S = S} {T=S = T=S} t = begin
      ι[ T=S ] mod-elim μ t
    ≅˘⟨ mod-β μ _ ⟩
      mod-elim μ (mod-intro μ (ι[ T=S ] mod-elim μ t))
    ≅˘⟨ mod-elim-cong μ (mod-intro-ι _) ⟩
      mod-elim μ (ι[ mod-cong T=S ] mod-intro μ (mod-elim μ t))
    ≅⟨ mod-elim-cong μ (ι-cong (mod-η μ t)) ⟩
      mod-elim μ (ι[ mod-cong T=S ] t) ∎
    where open ≅ᵗᵐ-Reasoning


--------------------------------------------------
-- Behaviour of DRAs with respect to semantic closed types

module _ (μ : Modality C D) {T : ClosedTy C} (clT : IsClosedNatural T) where
  mod-closed : IsClosedNatural ⟨ μ ∣ T ⟩
  IsClosedNatural.closed-natural mod-closed σ =
    transᵗʸ (mod-natural μ σ) (mod-cong μ (closed-natural clT (ctx-fmap (ctx-functor μ) σ)))
  IsClosedNatural.closed-id mod-closed =
    transᵉ (transᵗʸ-congʳ (mod-cong-cong μ (transᵉ (symᵉ (closed-subst-eq clT (lock-fmap-id μ)))
                                                   (transᵗʸ-congʳ (closed-id clT)))))
           (mod-natural-id μ)
  IsClosedNatural.closed-⊚ mod-closed τ σ  =
    transᵉ (transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-trans) (transᵉ transᵗʸ-assoc (transᵉ (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc)) (transᵉ (transᵗʸ-congʳ (transᵗʸ-congˡ (symᵉ (mod-natural-ty-eq μ σ _)))) (transᵉ (transᵗʸ-congʳ transᵗʸ-assoc) (symᵉ transᵗʸ-assoc))))))
           (transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ (mod-cong-trans μ)) (transᵉ (mod-cong-cong μ (closed-⊚ clT _ _)) (mod-cong-trans μ))))
                   (transᵉ (transᵉ (transᵉ (symᵉ transᵗʸ-assoc) (transᵗʸ-congˡ transᵗʸ-assoc)) (transᵗʸ-congˡ (mod-natural-⊚ μ τ σ)))
                           (transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ transᵗʸ-assoc)) (transᵗʸ-congʳ (transᵗʸ-congʳ (transᵉ (symᵉ (mod-cong-trans μ)) (mod-cong-cong μ (closed-subst-eq clT (lock-fmap-⊚ μ τ σ)))))))))
  IsClosedNatural.closed-subst-eq mod-closed ε =
    transᵉ (symᵉ transᵗʸ-assoc)
           (transᵉ (transᵗʸ-congˡ (mod-natural-subst-eq μ ε))
                   (transᵉ transᵗʸ-assoc
                           (transᵗʸ-congʳ (transᵉ (symᵉ (mod-cong-trans μ))
                                                  (mod-cong-cong μ (closed-subst-eq clT (lock-fmap-cong μ ε)))))))

  mod-intro-cl-natural : {Γ Δ : Ctx D} {σ : Γ ⇒ Δ} (t : Tm (Δ ,lock⟨ μ ⟩) T) →
                         (mod-intro μ t) [ mod-closed ∣ σ ]cl ≅ᵗᵐ mod-intro μ (t [ clT ∣ lock-fmap μ σ ]cl)
  mod-intro-cl-natural t =
    transᵗᵐ (ι⁻¹-cong (mod-intro-natural μ _ t))
    (transᵗᵐ ι⁻¹-trans
    (transᵗᵐ (ι⁻¹-cong ι-symˡ)
    (transᵗᵐ (ι-congᵉ (symᵉ (mod-cong-sym μ))) (mod-intro-ι μ _))))

  mod-elim-cl-natural : {Γ Δ : Ctx D} {σ : Γ ⇒ Δ} (t : Tm Δ ⟨ μ ∣ T ⟩) →
                        (mod-elim μ t) [ clT ∣ lock-fmap μ σ ]cl ≅ᵗᵐ mod-elim μ (t [ mod-closed ∣ σ ]cl)
  mod-elim-cl-natural t =
    transᵗᵐ (ι⁻¹-cong (mod-elim-natural μ _ t))
    (transᵗᵐ (mod-elim-ι μ _)
    (mod-elim-cong μ (transᵗᵐ (ι-congᵉ (mod-cong-sym μ)) (symᵗᵐ ι⁻¹-trans))))


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
    from-mod-⊠ p = pair (mod-intro μ (fst (mod-elim μ p))) (mod-intro μ (snd (mod-elim μ p)))

    to-mod-⊠ : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩) → Tm Γ ⟨ μ ∣ T ⊠ S ⟩
    to-mod-⊠ p = mod-intro μ (pair (mod-elim μ (fst p)) (mod-elim μ (snd p)))

    from-to-mod-⊠ : (p : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)) → from-mod-⊠ (to-mod-⊠ p) ≅ᵗᵐ p
    from-to-mod-⊠ p = let p' = pair (mod-elim μ (fst p)) (mod-elim μ (snd p)) in
      begin
        pair (mod-intro μ (fst (mod-elim μ (mod-intro μ p'))))
             (mod-intro μ (snd (mod-elim μ (mod-intro μ p'))))
      ≅⟨ pair-cong (mod-intro-cong μ (fst-cong (mod-β μ p')))
                   (mod-intro-cong μ (snd-cong (mod-β μ p'))) ⟩
        pair (mod-intro μ (fst p'))
             (mod-intro μ (snd p'))
      ≅⟨ pair-cong (mod-intro-cong μ (β-⊠-fst _ (mod-elim μ (snd p))))
                   (mod-intro-cong μ (β-⊠-snd (mod-elim μ (fst p)) _)) ⟩
        pair (mod-intro μ (mod-elim μ (fst p)))
             (mod-intro μ (mod-elim μ (snd p)))
      ≅⟨ pair-cong (mod-η μ (fst p)) (mod-η μ (snd p)) ⟩
        pair (fst p)
             (snd p)
      ≅˘⟨ η-⊠ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

    to-from-mod-⊠ : (p : Tm Γ ⟨ μ ∣ T ⊠ S ⟩) → to-mod-⊠ (from-mod-⊠ p) ≅ᵗᵐ p
    to-from-mod-⊠ p =
      let t = mod-intro μ (fst (mod-elim μ p))
          s = mod-intro μ (snd (mod-elim μ p))
      in begin
        mod-intro μ (pair (mod-elim μ (fst (pair t s)))
                          (mod-elim μ (snd (pair t s))))
      ≅⟨ mod-intro-cong μ (pair-cong (mod-elim-cong μ (β-⊠-fst t s))
                                     (mod-elim-cong μ (β-⊠-snd t s))) ⟩
        mod-intro μ (pair (mod-elim μ t)
                          (mod-elim μ s))
      ≅⟨ mod-intro-cong μ (pair-cong (mod-β μ _) (mod-β μ _)) ⟩
        mod-intro μ (pair (fst (mod-elim μ p))
                          (snd (mod-elim μ p)))
      ≅˘⟨ mod-intro-cong μ (η-⊠ (mod-elim μ p)) ⟩
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
mod-map 𝟙 φ = φ
mod-map-cong 𝟙 𝔢 = 𝔢
mod-map-id 𝟙 = reflⁿ
mod-map-⊙ 𝟙 = reflⁿ
mod-natural 𝟙 σ = reflᵗʸ
mod-natural-map 𝟙 σ η = transⁿ id-trans-unitʳ (symⁿ id-trans-unitˡ)
mod-natural-id-map 𝟙 = transⁿ id-trans-unitʳ (transⁿ (⊙-congʳ ty-subst-eq-subst-morph-refl) id-trans-unitʳ)
mod-natural-⊚-map 𝟙 τ σ = transⁿ
  (transⁿ (⊙-congʳ ty-subst-map-id) (transⁿ id-trans-unitʳ id-trans-unitʳ))
  (symⁿ (transⁿ (⊙-congˡ (transⁿ id-trans-unitʳ ty-subst-eq-subst-morph-refl)) id-trans-unitˡ))
mod-natural-subst-eq-map 𝟙 ε = transⁿ id-trans-unitˡ (symⁿ id-trans-unitʳ)
mod-intro 𝟙 t = t
mod-intro-cong 𝟙 t=t' = t=t'
mod-intro-natural 𝟙 σ t = symᵗᵐ ι-refl
mod-intro-convert 𝟙 t = reflᵗᵐ
mod-elim 𝟙 t = t
mod-elim-cong 𝟙 t=t' = t=t'
mod-β 𝟙 t = reflᵗᵐ
mod-η 𝟙 t = reflᵗᵐ


-- Composition of modalities
_ⓜ_ : {C1 C2 C3 : BaseCategory} → Modality C2 C3 → Modality C1 C2 → Modality C1 C3
ctx-functor (μ ⓜ ρ) = ctx-functor ρ ⓕ ctx-functor μ
⟨ μ ⓜ ρ ∣ T ⟩ = ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩
mod-map (μ ⓜ ρ) η = mod-map μ (mod-map ρ η)
mod-map-cong (μ ⓜ ρ) 𝔢 = mod-map-cong μ (mod-map-cong ρ 𝔢)
mod-map-id (μ ⓜ ρ) = transⁿ (mod-map-cong μ (mod-map-id ρ)) (mod-map-id μ)
mod-map-⊙ (μ ⓜ ρ) = transⁿ (mod-map-cong μ (mod-map-⊙ ρ)) (mod-map-⊙ μ)
mod-natural (μ ⓜ ρ) σ = transᵗʸ (mod-natural μ σ) (mod-cong μ (mod-natural ρ _))
mod-natural-map (μ ⓜ ρ) σ η =
    transⁿ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (symⁿ (mod-map-⊙ μ)))) (
  transⁿ (⊙-congˡ (mod-map-cong μ (mod-natural-map ρ _ η))) (
    transⁿ (transⁿ (⊙-congˡ (mod-map-⊙ μ)) ⊙-assoc) (
  transⁿ (⊙-congʳ (mod-natural-map μ σ (mod-map ρ η)))
    (symⁿ ⊙-assoc))))
mod-natural-id-map (μ ⓜ ρ) =
  transⁿ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (symⁿ (mod-map-⊙ μ)))) (
      transⁿ (⊙-congˡ (mod-map-cong μ (
          transⁿ (⊙-congˡ (transⁿ (mod-map-cong ρ (transⁿ (⊙-congʳ ty-subst-eq-subst-morph-trans) (symⁿ ⊙-assoc))) (mod-map-⊙ ρ))) (
        transⁿ ⊙-assoc (
          transⁿ (⊙-congʳ (symⁿ (mod-natural-subst-eq-map ρ _))) (
        transⁿ (symⁿ ⊙-assoc) (
          ⊙-congˡ (mod-natural-id-map ρ)))))))) (
  mod-natural-id-map μ))
mod-natural-⊚-map (μ ⓜ ρ) τ σ =
    transⁿ (transⁿ (⊙-congʳ ty-subst-map-⊙) (transⁿ (⊙-congˡ (symⁿ ⊙-assoc)) (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ ⊙-assoc)))) (
  transⁿ (⊙-congˡ (⊙-congʳ (symⁿ (mod-natural-map μ σ _)))) (
    transⁿ (⊙-congˡ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (transⁿ (⊙-congˡ (symⁿ (mod-map-⊙ μ))) (symⁿ (mod-map-⊙ μ)))))) (
  transⁿ (⊙-congˡ (⊙-congˡ (mod-map-cong μ (mod-natural-⊚-map ρ _ _)))) (
    transⁿ (transⁿ (⊙-congˡ (⊙-congˡ (mod-map-⊙ μ))) (transⁿ (⊙-congˡ ⊙-assoc) ⊙-assoc)) (
  transⁿ (⊙-congʳ (mod-natural-⊚-map μ τ σ)) (
    transⁿ (transⁿ (⊙-congʳ ⊙-assoc) (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (transⁿ (symⁿ (mod-map-⊙ μ)) (mod-map-cong μ ⊙-assoc))))) (
  transⁿ (⊙-congˡ (mod-map-cong μ (⊙-congʳ (mod-natural-subst-eq-map ρ _)))) (
    transⁿ (⊙-congˡ (transⁿ (mod-map-cong μ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (transⁿ (symⁿ (mod-map-⊙ ρ)) (mod-map-cong ρ (symⁿ ty-subst-eq-subst-morph-trans)))))) (mod-map-⊙ μ)))
    (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ ⊙-assoc))))))))))
mod-natural-subst-eq-map (μ ⓜ ρ) ε =
    transⁿ ⊙-assoc (
  transⁿ (⊙-congʳ (mod-natural-subst-eq-map μ ε)) (
    transⁿ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (symⁿ (mod-map-⊙ μ)))) (
  transⁿ (⊙-congˡ (mod-map-cong μ (mod-natural-subst-eq-map ρ _)))
    (transⁿ (⊙-congˡ (mod-map-⊙ μ)) ⊙-assoc))))
mod-intro (μ ⓜ ρ) t = mod-intro μ (mod-intro ρ t)
mod-intro-cong (μ ⓜ ρ) e = mod-intro-cong μ (mod-intro-cong ρ e)
mod-intro-natural (μ ⓜ ρ) σ t = begin
    (mod-intro μ (mod-intro ρ t)) [ σ ]'
  ≅⟨ mod-intro-natural μ σ (mod-intro ρ t) ⟩
    ι[ mod-natural μ σ ] mod-intro μ ((mod-intro ρ t) [ lock-fmap μ σ ]')
  ≅⟨ ι-cong (mod-intro-cong μ (mod-intro-natural ρ (lock-fmap μ σ) t)) ⟩
    ι[ mod-natural μ σ ] mod-intro μ (ι[ mod-natural ρ _ ] mod-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]'))
  ≅˘⟨ ι-cong (mod-intro-ι μ _) ⟩
    ι[ mod-natural μ σ ] (ι[ mod-cong μ (mod-natural ρ _) ] mod-intro μ (mod-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')))
  ≅˘⟨ ι-trans ⟩
    ι[ transᵗʸ (mod-natural μ σ) (mod-cong μ (mod-natural ρ (lock-fmap μ σ))) ] mod-intro μ (mod-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')) ∎
  where open ≅ᵗᵐ-Reasoning
mod-intro-convert (μ ⓜ ρ) t = transᵗᵐ (mod-intro-convert μ (mod-intro ρ t)) (mod-intro-cong μ (mod-intro-convert ρ t))
mod-elim (μ ⓜ ρ) t = mod-elim ρ (mod-elim μ t)
mod-elim-cong (μ ⓜ ρ) e = mod-elim-cong ρ (mod-elim-cong μ e)
mod-β (μ ⓜ ρ) t = transᵗᵐ (mod-elim-cong ρ (mod-β μ _)) (mod-β ρ t)
mod-η (μ ⓜ ρ) t = transᵗᵐ (mod-intro-cong μ (mod-η ρ _)) (mod-η μ t)


-- The unit modality or composition of modalities preserve the
-- structure of closed types being natural.
mod-cong-𝟙 : {Γ : Ctx C} {T S : Ty Γ} {e : T ≅ᵗʸ S} → mod-cong 𝟙 e ≅ᵉ e
from-eq mod-cong-𝟙 = reflⁿ

mod-cong-ⓜ : {ρ : Modality C D} {μ : Modality D E} {Γ : Ctx E} {T S : Ty (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)} {e : T ≅ᵗʸ S} →
             mod-cong (μ ⓜ ρ) e ≅ᵉ mod-cong μ (mod-cong ρ e)
from-eq mod-cong-ⓜ = reflⁿ

𝟙-preserves-cl : {A : ClosedTy C} (clA : IsClosedNatural A) → mod-closed 𝟙 clA ≅ᶜᵗʸ clA
closed-natural-eq (𝟙-preserves-cl clA) σ = transᵉ reflᵗʸ-unitˡ mod-cong-𝟙

ⓜ-preserves-cl : (μ : Modality D E) (ρ : Modality C D) {A : ClosedTy C} (clA : IsClosedNatural A) →
                 mod-closed (μ ⓜ ρ) clA ≅ᶜᵗʸ mod-closed μ (mod-closed ρ clA)
closed-natural-eq (ⓜ-preserves-cl μ ρ clA) σ =
  transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ (transᵗʸ-congʳ mod-cong-ⓜ) (symᵉ (mod-cong-trans μ))))


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
    ≅˘⟨ id-subst-unitʳ _ ⟩
      (from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ id-subst (lock μ Δ)
    ≅˘⟨ ⊚-congʳ (isoˡ (eq-lock Δ)) ⟩
      (from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ (to (eq-lock Δ) ⊚ from (eq-lock Δ))
    ≅˘⟨ ⊚-assoc ⟩
      ((from (eq-lock Γ) ⊚ lock-fmap μ σ) ⊚ to (eq-lock Δ)) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ ⊚-assoc ⟩
      (from (eq-lock Γ) ⊚ (lock-fmap μ σ ⊚ to (eq-lock Δ))) ⊚ from (eq-lock Δ)
    ≅˘⟨ ⊚-congˡ (⊚-congʳ (eq-lock-natural-to σ)) ⟩
      (from (eq-lock Γ) ⊚ (to (eq-lock Γ) ⊚ lock-fmap ρ σ)) ⊚ from (eq-lock Δ)
    ≅˘⟨ ⊚-congˡ ⊚-assoc ⟩
      ((from (eq-lock Γ) ⊚ to (eq-lock Γ)) ⊚ lock-fmap ρ σ) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ (⊚-congˡ (isoʳ (eq-lock Γ))) ⟩
      (id-subst (lock ρ Γ) ⊚ lock-fmap ρ σ) ⊚ from (eq-lock Δ)
    ≅⟨ ⊚-congˡ (id-subst-unitˡ _) ⟩
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

  eq-mod-closed : {A : ClosedTy C} → IsClosedNatural A → {Γ : Ctx D} → ⟨ μ ∣ A {Γ ,lock⟨ μ ⟩} ⟩ ≅ᵗʸ ⟨ ρ ∣ A ⟩
  eq-mod-closed {A = A} clA = begin
      ⟨ μ ∣ A ⟩
    ≅⟨ eq-mod-tyʳ A ⟩
      ⟨ ρ ∣ A [ to (eq-lock _) ] ⟩
    ≅⟨ mod-cong ρ (closed-natural clA (to (eq-lock _))) ⟩
      ⟨ ρ ∣ A ⟩ ∎
    where open ≅ᵗʸ-Reasoning

open _≅ᵐ_ public

reflᵐ : ∀ {C D} → {μ : Modality C D} → μ ≅ᵐ μ
eq-lock (reflᵐ {μ = μ}) Γ = reflᶜ
eq-lock-natural-to (reflᵐ {μ = μ}) σ = transˢ (id-subst-unitˡ _) (symˢ (id-subst-unitʳ _))
eq-mod-tyʳ (reflᵐ {μ = μ}) T = mod-cong μ (symᵗʸ (ty-subst-id T))

symᵐ : ∀ {C D} {μ ρ : Modality C D} → μ ≅ᵐ ρ → ρ ≅ᵐ μ
eq-lock (symᵐ e) Γ = symᶜ (eq-lock e Γ)
eq-lock-natural-to (symᵐ e) σ = eq-lock-natural-from e σ
eq-mod-tyʳ (symᵐ e) T = symᵗʸ (eq-mod-tyˡ e T)

transᵐ : ∀ {C D} {μ ρ κ : Modality C D} → μ ≅ᵐ ρ → ρ ≅ᵐ κ → μ ≅ᵐ κ
eq-lock (transᵐ μ=ρ ρ=κ) Γ = transᶜ (eq-lock μ=ρ Γ) (eq-lock ρ=κ Γ)
eq-lock-natural-to (transᵐ {μ = μ} {ρ} {κ} μ=ρ ρ=κ) σ = begin
    (to (eq-lock μ=ρ _) ⊚ to (eq-lock ρ=κ _)) ⊚ lock-fmap κ σ
  ≅⟨ ⊚-assoc ⟩
    to (eq-lock μ=ρ _) ⊚ (to (eq-lock ρ=κ _) ⊚ lock-fmap κ σ)
  ≅⟨ ⊚-congʳ (eq-lock-natural-to ρ=κ σ) ⟩
    to (eq-lock μ=ρ _) ⊚ (lock-fmap ρ σ ⊚ to (eq-lock ρ=κ _))
  ≅˘⟨ ⊚-assoc ⟩
    (to (eq-lock μ=ρ _) ⊚ lock-fmap ρ σ) ⊚ to (eq-lock ρ=κ _)
  ≅⟨ ⊚-congˡ (eq-lock-natural-to μ=ρ σ) ⟩
    (lock-fmap μ σ ⊚ to (eq-lock μ=ρ _)) ⊚ to (eq-lock ρ=κ _)
  ≅⟨ ⊚-assoc ⟩
    lock-fmap μ σ ⊚ (to (eq-lock μ=ρ _) ⊚ to (eq-lock ρ=κ _)) ∎
  where open ≅ˢ-Reasoning
eq-mod-tyʳ (transᵐ {μ = μ} {ρ = ρ} {κ = κ} μ=ρ ρ=κ) {Γ = Γ} T = begin
    ⟨ μ ∣ T ⟩
  ≅⟨ eq-mod-tyʳ μ=ρ T ⟩
    ⟨ ρ ∣ T [ to (eq-lock μ=ρ Γ) ] ⟩
  ≅⟨ eq-mod-tyʳ ρ=κ (T [ to (eq-lock μ=ρ Γ) ]) ⟩
    ⟨ κ ∣ (T [ to (eq-lock μ=ρ Γ) ]) [ to (eq-lock ρ=κ Γ) ] ⟩
  ≅⟨ mod-cong κ (ty-subst-comp T _ _) ⟩
    ⟨ κ ∣ T [ to (eq-lock μ=ρ Γ) ⊚ to (eq-lock ρ=κ Γ) ] ⟩ ∎
  where open ≅ᵗʸ-Reasoning

𝟙-unitʳ : (μ : Modality C D) → μ ⓜ 𝟙 ≅ᵐ μ
eq-lock (𝟙-unitʳ μ) Γ = reflᶜ
eq (eq-lock-natural-to (𝟙-unitʳ μ) σ) _ = refl
eq-mod-tyʳ (𝟙-unitʳ μ) T = symᵗʸ (mod-cong μ (ty-subst-id T))

𝟙-unitˡ : (μ : Modality C D) → 𝟙 ⓜ μ ≅ᵐ μ
eq-lock (𝟙-unitˡ μ) Γ = reflᶜ
eq (eq-lock-natural-to (𝟙-unitˡ μ) σ) _ = refl
eq-mod-tyʳ (𝟙-unitˡ μ) T = symᵗʸ (mod-cong μ (ty-subst-id T))

ⓜ-assoc : {C₁ C₂ C₃ C₄ : BaseCategory}
           (μ₃₄ : Modality C₃ C₄) (μ₂₃ : Modality C₂ C₃) (μ₁₂ : Modality C₁ C₂) →
           (μ₃₄ ⓜ μ₂₃) ⓜ μ₁₂ ≅ᵐ μ₃₄ ⓜ (μ₂₃ ⓜ μ₁₂)
eq-lock (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) Γ = reflᶜ
eq (eq-lock-natural-to (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) σ) _ = refl
eq-mod-tyʳ (ⓜ-assoc μ₃₄ μ₂₃ μ₁₂) T = symᵗʸ (mod-cong μ₃₄ (mod-cong μ₂₃ (mod-cong μ₁₂ (ty-subst-id T))))

ⓜ-congʳ : (ρ : Modality D E) {μ μ' : Modality C D} → μ ≅ᵐ μ' → ρ ⓜ μ ≅ᵐ ρ ⓜ μ'
eq-lock (ⓜ-congʳ ρ μ=μ') Γ = eq-lock μ=μ' (Γ ,lock⟨ ρ ⟩)
eq-lock-natural-to (ⓜ-congʳ ρ {μ} {μ'} μ=μ') σ = eq-lock-natural-to μ=μ' (lock-fmap ρ σ)
eq-mod-tyʳ (ⓜ-congʳ ρ μ=μ') T = mod-cong ρ (eq-mod-tyʳ μ=μ' T)

ⓜ-congˡ : {ρ ρ' : Modality D E} (μ : Modality C D) → ρ ≅ᵐ ρ' → ρ ⓜ μ ≅ᵐ ρ' ⓜ μ
from (eq-lock (ⓜ-congˡ μ ρ=ρ') Γ) = lock-fmap μ (from (eq-lock ρ=ρ' Γ))
to (eq-lock (ⓜ-congˡ μ ρ=ρ') Γ) = lock-fmap μ (to (eq-lock ρ=ρ' Γ))
isoˡ (eq-lock (ⓜ-congˡ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoˡ (eq-lock ρ=ρ' Γ))
isoʳ (eq-lock (ⓜ-congˡ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoʳ (eq-lock ρ=ρ' Γ))
eq-lock-natural-to (ⓜ-congˡ {ρ = ρ} {ρ'} μ ρ=ρ') σ = begin
    lock-fmap μ (to (eq-lock ρ=ρ' _)) ⊚ lock-fmap μ (lock-fmap ρ' σ)
  ≅˘⟨ lock-fmap-⊚ μ _ _ ⟩
    lock-fmap μ (to (eq-lock ρ=ρ' _) ⊚ lock-fmap ρ' σ)
  ≅⟨ lock-fmap-cong μ (eq-lock-natural-to ρ=ρ' σ) ⟩
    lock-fmap μ (lock-fmap ρ σ ⊚ to (eq-lock ρ=ρ' _))
  ≅⟨ lock-fmap-⊚ μ _ _ ⟩
    lock-fmap μ (lock-fmap ρ σ) ⊚ lock-fmap μ (to (eq-lock ρ=ρ' _)) ∎
  where open ≅ˢ-Reasoning
eq-mod-tyʳ (ⓜ-congˡ {ρ = ρ} {ρ' = ρ'} μ ρ=ρ') {Γ = Γ} T = begin
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
  step-≅ _ ρ≅κ μ≅ρ = transᵐ μ≅ρ ρ≅κ

  step-≅˘ : ∀ (μ {ρ κ} : Modality C D) → ρ ≅ᵐ κ → ρ ≅ᵐ μ → μ ≅ᵐ κ
  step-≅˘ _ ρ≅κ ρ≅μ = transᵐ (symᵐ ρ≅μ) ρ≅κ

  _∎ : ∀ (μ : Modality C D) → μ ≅ᵐ μ
  _∎ _ = reflᵐ

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

  key-subst : {Γ : Ctx D} → Γ ,lock⟨ ρ ⟩ ⇒ Γ ,lock⟨ μ ⟩
  key-subst {Γ = Γ} = transf-op transf Γ

  key-subst-natural : {Γ Δ : Ctx D} {σ : Γ ⇒ Δ} → key-subst {Δ} ⊚ lock-fmap ρ σ ≅ˢ lock-fmap μ σ ⊚ key-subst {Γ}
  key-subst-natural {σ = σ} = naturality transf σ

  coe-ty : {Γ : Ctx D} → Ty (Γ ,lock⟨ μ ⟩) → Ty (Γ ,lock⟨ ρ ⟩)
  coe-ty {Γ} T = T [ key-subst ]

  coe : {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ coe-ty T ⟩
  coe t = mod-intro ρ ((mod-elim μ t) [ key-subst ]')

  coe-closed : {T : ClosedTy C} → IsClosedNatural T → {Γ : Ctx D} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
  coe-closed {T = T} clT t = ι⁻¹[ mod-cong ρ (closed-natural clT key-subst) ] coe t

open TwoCell public


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


record _≅ᵗᶜ_ {μ ρ : Modality C D} (α β : TwoCell μ ρ) : Set₁ where
  field
    key-subst-eq : ∀ {Γ} → key-subst α {Γ} ≅ˢ key-subst β
open _≅ᵗᶜ_ public

module _ {μ ρ : Modality C D} where
  reflᵗᶜ : {α : TwoCell μ ρ} → α ≅ᵗᶜ α
  key-subst-eq reflᵗᶜ = reflˢ

  symᵗᶜ : {α β : TwoCell μ ρ} → α ≅ᵗᶜ β → β ≅ᵗᶜ α
  key-subst-eq (symᵗᶜ α=β) = symˢ (key-subst-eq α=β)

  transᵗᶜ : {α1 α2 α3 : TwoCell μ ρ} → α1 ≅ᵗᶜ α2 → α2 ≅ᵗᶜ α3 → α1 ≅ᵗᶜ α3
  key-subst-eq (transᵗᶜ e e') = transˢ (key-subst-eq e) (key-subst-eq e')

  ⓣ-vert-unitˡ : {α : TwoCell μ ρ} → id-cell ⓣ-vert α ≅ᵗᶜ α
  key-subst-eq ⓣ-vert-unitˡ = id-subst-unitʳ _

  ⓣ-vert-unitʳ : {α : TwoCell μ ρ} → α ⓣ-vert id-cell ≅ᵗᶜ α
  key-subst-eq ⓣ-vert-unitʳ = id-subst-unitˡ _

ⓣ-vert-assoc : {μ ρ κ φ : Modality C D} {α : TwoCell μ ρ} {β : TwoCell ρ κ} {γ : TwoCell κ φ} →
               (γ ⓣ-vert β) ⓣ-vert α ≅ᵗᶜ γ ⓣ-vert (β ⓣ-vert α)
key-subst-eq ⓣ-vert-assoc = symˢ ⊚-assoc

ⓣ-vert-congˡ : {μ ρ κ : Modality C D} {α α' : TwoCell ρ κ} {β : TwoCell μ ρ} →
               α ≅ᵗᶜ α' → α ⓣ-vert β ≅ᵗᶜ α' ⓣ-vert β
key-subst-eq (ⓣ-vert-congˡ e) = ⊚-congʳ (key-subst-eq e)

ⓣ-vert-congʳ : {μ ρ κ : Modality C D} {α : TwoCell ρ κ} {β β' : TwoCell μ ρ} →
               β ≅ᵗᶜ β' → α ⓣ-vert β ≅ᵗᶜ α ⓣ-vert β'
key-subst-eq (ⓣ-vert-congʳ e) = ⊚-congˡ (key-subst-eq e)

ⓣ-hor-congˡ : {μ ρ : Modality C D} {κ φ : Modality D E} {α : TwoCell μ ρ} {β β' : TwoCell κ φ} →
              β ≅ᵗᶜ β' → β ⓣ-hor α ≅ᵗᶜ β' ⓣ-hor α
key-subst-eq (ⓣ-hor-congˡ {ρ = ρ} e) = ⊚-congʳ (lock-fmap-cong ρ (key-subst-eq e))

ⓣ-hor-congʳ : {μ ρ : Modality C D} {κ φ : Modality D E} {α α' : TwoCell μ ρ} {β : TwoCell κ φ} →
              α ≅ᵗᶜ α' → β ⓣ-hor α ≅ᵗᶜ β ⓣ-hor α'
key-subst-eq (ⓣ-hor-congʳ e) = ⊚-congˡ (key-subst-eq e)

ⓣ-hor-id : {μ : Modality C D} {ρ : Modality D E} → id-cell {μ = ρ} ⓣ-hor id-cell {μ = μ} ≅ᵗᶜ id-cell
key-subst-eq (ⓣ-hor-id {μ = μ}) = transˢ (id-subst-unitˡ _) (lock-fmap-id μ)

2-cell-interchange : {μ μ' μ'' : Modality D E} {ρ ρ' ρ'' : Modality C D}
                     {α : TwoCell μ μ'} {β : TwoCell μ' μ''} {γ : TwoCell ρ ρ'} {δ : TwoCell ρ' ρ''} →
                     (β ⓣ-vert α) ⓣ-hor (δ ⓣ-vert γ) ≅ᵗᶜ (β ⓣ-hor δ) ⓣ-vert (α ⓣ-hor γ)
key-subst-eq (2-cell-interchange {ρ'' = ρ''} {δ = δ}) =
  transˢ (⊚-congʳ (lock-fmap-⊚ ρ'' _ _)) (
  transˢ ⊚-assoc (
  transˢ (⊚-congʳ (transˢ (symˢ ⊚-assoc) (⊚-congˡ (naturality (transf δ) _)))) (
  transˢ (⊚-congʳ ⊚-assoc) (
  symˢ ⊚-assoc))))

ⓣ-hor-unitˡ : {μ ρ : Modality C D} {α : TwoCell μ ρ} →
              ≅ᵐ-to-2-cell (𝟙-unitˡ ρ) ⓣ-vert (id-cell {μ = 𝟙} ⓣ-hor α) ≅ᵗᶜ α ⓣ-vert ≅ᵐ-to-2-cell (𝟙-unitˡ μ)
key-subst-eq (ⓣ-hor-unitˡ {ρ = ρ}) =
  transˢ (id-subst-unitʳ _) (transˢ (⊚-congʳ (lock-fmap-id ρ)) (transˢ (id-subst-unitʳ _) (symˢ (id-subst-unitˡ _))))

ⓣ-hor-unitʳ : {μ ρ : Modality C D} {α : TwoCell μ ρ} →
              ≅ᵐ-to-2-cell (𝟙-unitʳ ρ) ⓣ-vert (α ⓣ-hor id-cell {μ = 𝟙}) ≅ᵗᶜ α ⓣ-vert ≅ᵐ-to-2-cell (𝟙-unitʳ μ)
key-subst-eq (ⓣ-hor-unitʳ {ρ = ρ}) = id-subst-unitʳ _

ⓣ-hor-assoc : {F : BaseCategory}
              {μ μ' : Modality C D} {ρ ρ' : Modality D E} {κ κ' : Modality E F}
              {α : TwoCell μ μ'} {β : TwoCell ρ ρ'} {γ : TwoCell κ κ'} →
              ≅ᵐ-to-2-cell (ⓜ-assoc _ _ _) ⓣ-vert ((γ ⓣ-hor β) ⓣ-hor α) ≅ᵗᶜ (γ ⓣ-hor (β ⓣ-hor α)) ⓣ-vert ≅ᵐ-to-2-cell (ⓜ-assoc _ _ _)
key-subst-eq (ⓣ-hor-assoc {μ' = μ'}) =
  transˢ (id-subst-unitʳ _) (transˢ (⊚-congʳ (lock-fmap-⊚ μ' _ _)) (transˢ (symˢ ⊚-assoc) (symˢ (id-subst-unitˡ _))))
