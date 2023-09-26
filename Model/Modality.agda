--------------------------------------------------
-- Definition and properties of dependent adjunctions
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

infix 1 _≅ᵈ_ _≅ᵗᶜ_
infixl 20 _ⓓ_ _ⓣ-vert_ _ⓣ-hor_


--------------------------------------------------
-- Definition of a modality as a dependent right adjoint

record DRA (C D : BaseCategory) : Set₁ where
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
    dra-map : {Γ : Ctx D} {T S : Ty (lock Γ)} →
              (T ↣ S) → ⟨_∣_⟩ T ↣ ⟨_∣_⟩ S
    dra-map-cong : {Γ : Ctx D} {T S : Ty (lock Γ)} {φ η : T ↣ S} → φ ≅ⁿ η →
                   dra-map φ ≅ⁿ dra-map η
    dra-map-id : {Γ : Ctx D} {T : Ty (lock Γ)} → dra-map (id-trans T) ≅ⁿ id-trans (⟨_∣_⟩ T)
    dra-map-⊙ : {Γ : Ctx D} {R T S : Ty (lock Γ)} {φ : T ↣ S} {η : R ↣ T} →
                dra-map (φ ⊙ η) ≅ⁿ dra-map φ ⊙ dra-map η

    -- We can push substitutions under the modal type former but they
    -- get locked. Again, this must happen in a coherent way (i.e. the
    -- modal type former is a pseudonatural transformation from the
    -- pseudofunctor Ty ∘ lock to Ty).
    dra-natural : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T : Ty (lock Δ)} →
                  (⟨_∣_⟩ T) [ σ ] ≅ᵗʸ ⟨_∣_⟩ (T [ lock-fmap σ ])
    dra-natural-map : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T S : Ty (lock Δ)} (η : T ↣ S) →
                      dra-map (ty-subst-map (lock-fmap σ) η) ⊙ from (dra-natural σ {T = T})
                        ≅ⁿ
                      from (dra-natural σ) ⊙ ty-subst-map σ (dra-map η)
    dra-natural-id-map : {Γ : Ctx D} {T : Ty (lock Γ)} →
                         dra-map (from (ty-subst-id T) ⊙ ty-subst-eq-subst-morph lock-fmap-id T) ⊙ from (dra-natural (id-subst Γ))
                           ≅ⁿ
                         from (ty-subst-id (⟨_∣_⟩ T))
    dra-natural-⊚-map : {Γ Δ Θ : Ctx D} (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (lock Θ)} →
                        dra-map (from (ty-subst-comp T (lock-fmap τ) (lock-fmap σ))) ⊙ from (dra-natural σ) ⊙ ty-subst-map σ (from (dra-natural τ))
                          ≅ⁿ
                        dra-map (ty-subst-eq-subst-morph (lock-fmap-⊚ τ σ) T) ⊙ from (dra-natural (τ ⊚ σ)) ⊙ from (ty-subst-comp (⟨_∣_⟩ T) τ σ)
    dra-natural-subst-eq-map : {Γ Δ : Ctx D} {σ τ : Γ ⇒ Δ} {T : Ty (lock Δ)} (ε : σ ≅ˢ τ) →
                               from (dra-natural τ) ⊙ ty-subst-eq-subst-morph ε (⟨_∣_⟩ T)
                                 ≅ⁿ
                               dra-map (ty-subst-eq-subst-morph (lock-fmap-cong ε) T) ⊙ from (dra-natural σ)

    -- Term formers coming with a modality and their laws.
    dra-intro : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm (lock Γ) T → Tm Γ (⟨_∣_⟩ T)
    dra-intro-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm (lock Γ) T} →
                     t ≅ᵗᵐ t' → dra-intro t ≅ᵗᵐ dra-intro t'
    dra-intro-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
                        (dra-intro t) [ σ ]' ≅ᵗᵐ ι[ dra-natural σ ] dra-intro (t [ lock-fmap σ ]')
    dra-intro-convert : {Γ : Ctx D} {T S : Ty (lock Γ)} {η : T ↣ S} (t : Tm (lock Γ) T) →
                        convert-term (dra-map η) (dra-intro t) ≅ᵗᵐ dra-intro (convert-term η t)

    dra-elim : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm Γ (⟨_∣_⟩ T) → Tm (lock Γ) T
    dra-elim-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm Γ (⟨_∣_⟩ T)} →
                    t ≅ᵗᵐ t' → dra-elim t ≅ᵗᵐ dra-elim t'
    -- Naturality of dra-elim and the fact that it commutes with convert-term can be proved
    -- from dra-intro-natural, dra-intro-convert and the β and η laws (see below).

    dra-β : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
            dra-elim (dra-intro t) ≅ᵗᵐ t
    dra-η : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
            dra-intro (dra-elim t) ≅ᵗᵐ t

open DRA public
_,lock⟨_⟩ : Ctx D → DRA C D → Ctx C
Γ ,lock⟨ μ ⟩ = lock μ Γ


module _ (μ : DRA C D) where
  dra-cong : {Γ : Ctx D} {T S : Ty (lock μ Γ)} →
             T ≅ᵗʸ S → ⟨ μ ∣ T ⟩ ≅ᵗʸ ⟨ μ ∣ S ⟩
  from (dra-cong e) = dra-map μ (from e)
  to (dra-cong e) = dra-map μ (to e)
  isoˡ (dra-cong e) = transⁿ (symⁿ (dra-map-⊙ μ)) (transⁿ (dra-map-cong μ (isoˡ e)) (dra-map-id μ))
  isoʳ (dra-cong e) = transⁿ (symⁿ (dra-map-⊙ μ)) (transⁿ (dra-map-cong μ (isoʳ e)) (dra-map-id μ))

  dra-cong-refl : {Γ : Ctx D} {T : Ty (lock μ Γ)} → dra-cong (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
  from-eq dra-cong-refl = dra-map-id μ

  dra-cong-sym : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {e : T ≅ᵗʸ S} → dra-cong (symᵗʸ e) ≅ᵉ symᵗʸ (dra-cong e)
  from-eq dra-cong-sym = reflⁿ

  dra-cong-trans : {Γ : Ctx D} {R T S : Ty (lock μ Γ)} {e : R ≅ᵗʸ T} {e' : T ≅ᵗʸ S} →
                   dra-cong (transᵗʸ e e') ≅ᵉ transᵗʸ (dra-cong e) (dra-cong e')
  from-eq dra-cong-trans = dra-map-⊙ μ

  dra-cong-cong : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → dra-cong e ≅ᵉ dra-cong e'
  from-eq (dra-cong-cong 𝑒) = dra-map-cong μ (from-eq 𝑒)

  dra-natural-ty-eq : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T S : Ty (lock μ Δ)} (e : T ≅ᵗʸ S) →
                      transᵗʸ (dra-natural μ σ {T = T}) (dra-cong (ty-subst-cong-ty (lock-fmap μ σ) e))
                        ≅ᵉ
                      transᵗʸ (ty-subst-cong-ty σ (dra-cong e)) (dra-natural μ σ)
  from-eq (dra-natural-ty-eq σ e) = dra-natural-map μ σ (from e)

  dra-natural-id : {Γ : Ctx D} {T : Ty (lock μ Γ)} →
                   transᵗʸ (dra-natural μ _) (dra-cong (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) T) (ty-subst-id T)))
                     ≅ᵉ
                   ty-subst-id ⟨ μ ∣ T ⟩
  from-eq dra-natural-id = dra-natural-id-map μ

  dra-natural-⊚ : {Γ Δ Θ : Ctx D} (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (lock μ Θ)} →
                  transᵗʸ (ty-subst-cong-ty σ (dra-natural μ τ)) (transᵗʸ (dra-natural μ σ) (dra-cong (ty-subst-comp T _ _)))
                    ≅ᵉ
                  transᵗʸ (ty-subst-comp ⟨ μ ∣ T ⟩ τ σ) (transᵗʸ (dra-natural μ (τ ⊚ σ)) (dra-cong (ty-subst-cong-subst (lock-fmap-⊚ μ τ σ) T)))
  from-eq (dra-natural-⊚ τ σ) = dra-natural-⊚-map μ τ σ

  dra-natural-subst-eq : {Γ Δ : Ctx D} {σ τ : Γ ⇒ Δ} {T : Ty (lock μ Δ)} (ε : σ ≅ˢ τ) →
                         transᵗʸ (ty-subst-cong-subst ε ⟨ μ ∣ T ⟩) (dra-natural μ τ)
                           ≅ᵉ
                         transᵗʸ (dra-natural μ σ) (dra-cong (ty-subst-cong-subst (lock-fmap-cong μ ε) T))
  from-eq (dra-natural-subst-eq ε) = dra-natural-subst-eq-map μ ε


  dra-intro-ι : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {T=S : T ≅ᵗʸ S} (t : Tm (lock μ Γ) S) →
                ι[ dra-cong T=S ] dra-intro μ t ≅ᵗᵐ dra-intro μ (ι[ T=S ] t)
  dra-intro-ι t = transᵗᵐ ι-convert (transᵗᵐ (dra-intro-convert μ t) (dra-intro-cong μ (symᵗᵐ ι-convert)))

  dra-elim-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock μ Γ)} (t : Tm Γ ⟨ μ ∣ T ⟩) →
                     (dra-elim μ t) [ lock-fmap μ σ ]' ≅ᵗᵐ dra-elim μ (ι⁻¹[ dra-natural μ σ ] (t [ σ ]'))
  dra-elim-natural σ t = begin
      (dra-elim μ t) [ lock-fmap μ σ ]'
    ≅˘⟨ dra-β μ _ ⟩
      dra-elim μ (dra-intro μ ((dra-elim μ t) [ lock-fmap μ σ ]'))
    ≅˘⟨ dra-elim-cong μ ι-symˡ ⟩
      dra-elim μ (ι⁻¹[ dra-natural μ σ ] (ι[ dra-natural μ σ ] (dra-intro μ ((dra-elim μ t) [ lock-fmap μ σ ]'))))
    ≅˘⟨ dra-elim-cong μ (ι⁻¹-cong (dra-intro-natural μ σ (dra-elim μ t))) ⟩
      dra-elim μ (ι⁻¹[ dra-natural μ σ ] (dra-intro μ (dra-elim μ t) [ σ ]'))
    ≅⟨ dra-elim-cong μ (ι⁻¹-cong (tm-subst-cong-tm σ (dra-η μ t))) ⟩
      dra-elim μ (ι⁻¹[ dra-natural μ σ ] (t [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning

  dra-elim-ι : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {T=S : T ≅ᵗʸ S} (t : Tm Γ ⟨ μ ∣ S ⟩) →
               ι[ T=S ] dra-elim μ t ≅ᵗᵐ dra-elim μ (ι[ dra-cong T=S ] t)
  dra-elim-ι {T = T} {S = S} {T=S = T=S} t = begin
      ι[ T=S ] dra-elim μ t
    ≅˘⟨ dra-β μ _ ⟩
      dra-elim μ (dra-intro μ (ι[ T=S ] dra-elim μ t))
    ≅˘⟨ dra-elim-cong μ (dra-intro-ι _) ⟩
      dra-elim μ (ι[ dra-cong T=S ] dra-intro μ (dra-elim μ t))
    ≅⟨ dra-elim-cong μ (ι-cong (dra-η μ t)) ⟩
      dra-elim μ (ι[ dra-cong T=S ] t) ∎
    where open ≅ᵗᵐ-Reasoning


--------------------------------------------------
-- Behaviour of DRAs with respect to semantic closed types

module _ (μ : DRA C D) {T : ClosedTy C} (clT : IsClosedNatural T) where
  dra-closed : IsClosedNatural ⟨ μ ∣ T ⟩
  IsClosedNatural.closed-natural dra-closed σ =
    transᵗʸ (dra-natural μ σ) (dra-cong μ (closed-natural clT (ctx-fmap (ctx-functor μ) σ)))
  IsClosedNatural.closed-id dra-closed =
    transᵉ (transᵗʸ-congʳ (dra-cong-cong μ (transᵉ (symᵉ (closed-subst-eq clT (lock-fmap-id μ)))
                                                   (transᵗʸ-congʳ (closed-id clT)))))
           (dra-natural-id μ)
  IsClosedNatural.closed-⊚ dra-closed τ σ  =
    transᵉ (transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-trans) (transᵉ transᵗʸ-assoc (transᵉ (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc)) (transᵉ (transᵗʸ-congʳ (transᵗʸ-congˡ (symᵉ (dra-natural-ty-eq μ σ _)))) (transᵉ (transᵗʸ-congʳ transᵗʸ-assoc) (symᵉ transᵗʸ-assoc))))))
           (transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans μ)) (transᵉ (dra-cong-cong μ (closed-⊚ clT _ _)) (dra-cong-trans μ))))
                   (transᵉ (transᵉ (transᵉ (symᵉ transᵗʸ-assoc) (transᵗʸ-congˡ transᵗʸ-assoc)) (transᵗʸ-congˡ (dra-natural-⊚ μ τ σ)))
                           (transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ transᵗʸ-assoc)) (transᵗʸ-congʳ (transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans μ)) (dra-cong-cong μ (closed-subst-eq clT (lock-fmap-⊚ μ τ σ)))))))))
  IsClosedNatural.closed-subst-eq dra-closed ε =
    transᵉ (symᵉ transᵗʸ-assoc)
           (transᵉ (transᵗʸ-congˡ (dra-natural-subst-eq μ ε))
                   (transᵉ transᵗʸ-assoc
                           (transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans μ))
                                                  (dra-cong-cong μ (closed-subst-eq clT (lock-fmap-cong μ ε)))))))

  dra-intro-cl-natural : {Γ Δ : Ctx D} {σ : Γ ⇒ Δ} (t : Tm (Δ ,lock⟨ μ ⟩) T) →
                         (dra-intro μ t) [ dra-closed ∣ σ ]cl ≅ᵗᵐ dra-intro μ (t [ clT ∣ lock-fmap μ σ ]cl)
  dra-intro-cl-natural t =
    transᵗᵐ (ι⁻¹-cong (dra-intro-natural μ _ t))
    (transᵗᵐ ι⁻¹-trans
    (transᵗᵐ (ι⁻¹-cong ι-symˡ)
    (transᵗᵐ (ι-congᵉ (symᵉ (dra-cong-sym μ))) (dra-intro-ι μ _))))

  dra-elim-cl-natural : {Γ Δ : Ctx D} {σ : Γ ⇒ Δ} (t : Tm Δ ⟨ μ ∣ T ⟩) →
                        (dra-elim μ t) [ clT ∣ lock-fmap μ σ ]cl ≅ᵗᵐ dra-elim μ (t [ dra-closed ∣ σ ]cl)
  dra-elim-cl-natural t =
    transᵗᵐ (ι⁻¹-cong (dra-elim-natural μ _ t))
    (transᵗᵐ (dra-elim-ι μ _)
    (dra-elim-cong μ (transᵗᵐ (ι-congᵉ (dra-cong-sym μ)) (symᵗᵐ ι⁻¹-trans))))


--------------------------------------------------
-- Properties of DRAs with respect to functions, products, ...

module _ (μ : DRA C D) {Γ : Ctx D} where

  module _ {T S : Ty (Γ ,lock⟨ μ ⟩)} where

    -- A DRA is a functor (at the term level).
    dra-tm-map : Tm (Γ ,lock⟨ μ ⟩) (T ⇛ S) → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
    dra-tm-map f t = dra-intro μ (f $ dra-elim μ t)

    infixl 12 dra-tm-map
    syntax dra-tm-map μ f t = f ⟨$- μ ⟩ t

    -- A DRA is also an applicative functor.
    dra-⊛ : Tm Γ ⟨ μ ∣ T ⇛ S ⟩ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
    dra-⊛ f t = dra-intro μ (dra-elim μ f $ dra-elim μ t)

    infixl 12 dra-⊛
    syntax dra-⊛ μ f t = f ⊛⟨ μ ⟩ t

    -- DRAs preserve products (up to isomorphism).
    from-dra-⊠ : Tm Γ ⟨ μ ∣ T ⊠ S ⟩ → Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)
    from-dra-⊠ p = pair (dra-intro μ (fst (dra-elim μ p))) (dra-intro μ (snd (dra-elim μ p)))

    to-dra-⊠ : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩) → Tm Γ ⟨ μ ∣ T ⊠ S ⟩
    to-dra-⊠ p = dra-intro μ (pair (dra-elim μ (fst p)) (dra-elim μ (snd p)))

    from-to-dra-⊠ : (p : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)) → from-dra-⊠ (to-dra-⊠ p) ≅ᵗᵐ p
    from-to-dra-⊠ p = let p' = pair (dra-elim μ (fst p)) (dra-elim μ (snd p)) in
      begin
        pair (dra-intro μ (fst (dra-elim μ (dra-intro μ p'))))
             (dra-intro μ (snd (dra-elim μ (dra-intro μ p'))))
      ≅⟨ pair-cong (dra-intro-cong μ (fst-cong (dra-β μ p')))
                   (dra-intro-cong μ (snd-cong (dra-β μ p'))) ⟩
        pair (dra-intro μ (fst p'))
             (dra-intro μ (snd p'))
      ≅⟨ pair-cong (dra-intro-cong μ (β-⊠-fst _ (dra-elim μ (snd p))))
                   (dra-intro-cong μ (β-⊠-snd (dra-elim μ (fst p)) _)) ⟩
        pair (dra-intro μ (dra-elim μ (fst p)))
             (dra-intro μ (dra-elim μ (snd p)))
      ≅⟨ pair-cong (dra-η μ (fst p)) (dra-η μ (snd p)) ⟩
        pair (fst p)
             (snd p)
      ≅˘⟨ η-⊠ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

    to-from-dra-⊠ : (p : Tm Γ ⟨ μ ∣ T ⊠ S ⟩) → to-dra-⊠ (from-dra-⊠ p) ≅ᵗᵐ p
    to-from-dra-⊠ p =
      let t = dra-intro μ (fst (dra-elim μ p))
          s = dra-intro μ (snd (dra-elim μ p))
      in begin
        dra-intro μ (pair (dra-elim μ (fst (pair t s)))
                          (dra-elim μ (snd (pair t s))))
      ≅⟨ dra-intro-cong μ (pair-cong (dra-elim-cong μ (β-⊠-fst t s))
                                     (dra-elim-cong μ (β-⊠-snd t s))) ⟩
        dra-intro μ (pair (dra-elim μ t)
                          (dra-elim μ s))
      ≅⟨ dra-intro-cong μ (pair-cong (dra-β μ _) (dra-β μ _)) ⟩
        dra-intro μ (pair (fst (dra-elim μ p))
                          (snd (dra-elim μ p)))
      ≅˘⟨ dra-intro-cong μ (η-⊠ (dra-elim μ p)) ⟩
        dra-intro μ (dra-elim μ p)
      ≅⟨ dra-η μ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

  -- DRAs preserve the unit type (up to isomorphism).
  dra-unit' : Tm Γ ⟨ μ ∣ Unit' ⟩
  dra-unit' = dra-intro μ tt'

  dra-unit'-η : (t : Tm Γ ⟨ μ ∣ Unit' ⟩) → t ≅ᵗᵐ dra-unit'
  dra-unit'-η t =
    begin
      t
    ≅˘⟨ dra-η μ t ⟩
      dra-intro μ (dra-elim μ t)
    ≅⟨ dra-intro-cong μ (η-unit (dra-elim μ t)) ⟩
      dra-intro μ tt' ∎
    where open ≅ᵗᵐ-Reasoning


--------------------------------------------------
-- Constructing new DRAs

-- The unit DRA
𝟙 : {C : BaseCategory} → DRA C C
ctx-functor 𝟙 = id-ctx-functor
⟨ 𝟙 ∣ T ⟩ = T
dra-map 𝟙 φ = φ
dra-map-cong 𝟙 𝔢 = 𝔢
dra-map-id 𝟙 = reflⁿ
dra-map-⊙ 𝟙 = reflⁿ
dra-natural 𝟙 σ = reflᵗʸ
dra-natural-map 𝟙 σ η = transⁿ id-trans-unitʳ (symⁿ id-trans-unitˡ)
dra-natural-id-map 𝟙 = transⁿ id-trans-unitʳ (transⁿ (⊙-congʳ ty-subst-eq-subst-morph-refl) id-trans-unitʳ)
dra-natural-⊚-map 𝟙 τ σ = transⁿ
  (transⁿ (⊙-congʳ ty-subst-map-id) (transⁿ id-trans-unitʳ id-trans-unitʳ))
  (symⁿ (transⁿ (⊙-congˡ (transⁿ id-trans-unitʳ ty-subst-eq-subst-morph-refl)) id-trans-unitˡ))
dra-natural-subst-eq-map 𝟙 ε = transⁿ id-trans-unitˡ (symⁿ id-trans-unitʳ)
dra-intro 𝟙 t = t
dra-intro-cong 𝟙 t=t' = t=t'
dra-intro-natural 𝟙 σ t = symᵗᵐ ι-refl
dra-intro-convert 𝟙 t = reflᵗᵐ
dra-elim 𝟙 t = t
dra-elim-cong 𝟙 t=t' = t=t'
dra-β 𝟙 t = reflᵗᵐ
dra-η 𝟙 t = reflᵗᵐ


-- Composition of DRAs
_ⓓ_ : {C1 C2 C3 : BaseCategory} → DRA C2 C3 → DRA C1 C2 → DRA C1 C3
ctx-functor (μ ⓓ ρ) = ctx-functor ρ ⓕ ctx-functor μ
⟨ μ ⓓ ρ ∣ T ⟩ = ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩
dra-map (μ ⓓ ρ) η = dra-map μ (dra-map ρ η)
dra-map-cong (μ ⓓ ρ) 𝔢 = dra-map-cong μ (dra-map-cong ρ 𝔢)
dra-map-id (μ ⓓ ρ) = transⁿ (dra-map-cong μ (dra-map-id ρ)) (dra-map-id μ)
dra-map-⊙ (μ ⓓ ρ) = transⁿ (dra-map-cong μ (dra-map-⊙ ρ)) (dra-map-⊙ μ)
dra-natural (μ ⓓ ρ) σ = transᵗʸ (dra-natural μ σ) (dra-cong μ (dra-natural ρ _))
dra-natural-map (μ ⓓ ρ) σ η =
    transⁿ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (symⁿ (dra-map-⊙ μ)))) (
  transⁿ (⊙-congˡ (dra-map-cong μ (dra-natural-map ρ _ η))) (
    transⁿ (transⁿ (⊙-congˡ (dra-map-⊙ μ)) ⊙-assoc) (
  transⁿ (⊙-congʳ (dra-natural-map μ σ (dra-map ρ η)))
    (symⁿ ⊙-assoc))))
dra-natural-id-map (μ ⓓ ρ) =
  transⁿ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (symⁿ (dra-map-⊙ μ)))) (
      transⁿ (⊙-congˡ (dra-map-cong μ (
          transⁿ (⊙-congˡ (transⁿ (dra-map-cong ρ (transⁿ (⊙-congʳ ty-subst-eq-subst-morph-trans) (symⁿ ⊙-assoc))) (dra-map-⊙ ρ))) (
        transⁿ ⊙-assoc (
          transⁿ (⊙-congʳ (symⁿ (dra-natural-subst-eq-map ρ _))) (
        transⁿ (symⁿ ⊙-assoc) (
          ⊙-congˡ (dra-natural-id-map ρ)))))))) (
  dra-natural-id-map μ))
dra-natural-⊚-map (μ ⓓ ρ) τ σ =
    transⁿ (transⁿ (⊙-congʳ ty-subst-map-⊙) (transⁿ (⊙-congˡ (symⁿ ⊙-assoc)) (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ ⊙-assoc)))) (
  transⁿ (⊙-congˡ (⊙-congʳ (symⁿ (dra-natural-map μ σ _)))) (
    transⁿ (⊙-congˡ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (transⁿ (⊙-congˡ (symⁿ (dra-map-⊙ μ))) (symⁿ (dra-map-⊙ μ)))))) (
  transⁿ (⊙-congˡ (⊙-congˡ (dra-map-cong μ (dra-natural-⊚-map ρ _ _)))) (
    transⁿ (transⁿ (⊙-congˡ (⊙-congˡ (dra-map-⊙ μ))) (transⁿ (⊙-congˡ ⊙-assoc) ⊙-assoc)) (
  transⁿ (⊙-congʳ (dra-natural-⊚-map μ τ σ)) (
    transⁿ (transⁿ (⊙-congʳ ⊙-assoc) (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (transⁿ (symⁿ (dra-map-⊙ μ)) (dra-map-cong μ ⊙-assoc))))) (
  transⁿ (⊙-congˡ (dra-map-cong μ (⊙-congʳ (dra-natural-subst-eq-map ρ _)))) (
    transⁿ (⊙-congˡ (transⁿ (dra-map-cong μ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (transⁿ (symⁿ (dra-map-⊙ ρ)) (dra-map-cong ρ (symⁿ ty-subst-eq-subst-morph-trans)))))) (dra-map-⊙ μ)))
    (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ ⊙-assoc))))))))))
dra-natural-subst-eq-map (μ ⓓ ρ) ε =
    transⁿ ⊙-assoc (
  transⁿ (⊙-congʳ (dra-natural-subst-eq-map μ ε)) (
    transⁿ (transⁿ (symⁿ ⊙-assoc) (⊙-congˡ (symⁿ (dra-map-⊙ μ)))) (
  transⁿ (⊙-congˡ (dra-map-cong μ (dra-natural-subst-eq-map ρ _)))
    (transⁿ (⊙-congˡ (dra-map-⊙ μ)) ⊙-assoc))))
dra-intro (μ ⓓ ρ) t = dra-intro μ (dra-intro ρ t)
dra-intro-cong (μ ⓓ ρ) e = dra-intro-cong μ (dra-intro-cong ρ e)
dra-intro-natural (μ ⓓ ρ) σ t = begin
    (dra-intro μ (dra-intro ρ t)) [ σ ]'
  ≅⟨ dra-intro-natural μ σ (dra-intro ρ t) ⟩
    ι[ dra-natural μ σ ] dra-intro μ ((dra-intro ρ t) [ lock-fmap μ σ ]')
  ≅⟨ ι-cong (dra-intro-cong μ (dra-intro-natural ρ (lock-fmap μ σ) t)) ⟩
    ι[ dra-natural μ σ ] dra-intro μ (ι[ dra-natural ρ _ ] dra-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]'))
  ≅˘⟨ ι-cong (dra-intro-ι μ _) ⟩
    ι[ dra-natural μ σ ] (ι[ dra-cong μ (dra-natural ρ _) ] dra-intro μ (dra-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')))
  ≅˘⟨ ι-trans ⟩
    ι[ transᵗʸ (dra-natural μ σ) (dra-cong μ (dra-natural ρ (lock-fmap μ σ))) ] dra-intro μ (dra-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')) ∎
  where open ≅ᵗᵐ-Reasoning
dra-intro-convert (μ ⓓ ρ) t = transᵗᵐ (dra-intro-convert μ (dra-intro ρ t)) (dra-intro-cong μ (dra-intro-convert ρ t))
dra-elim (μ ⓓ ρ) t = dra-elim ρ (dra-elim μ t)
dra-elim-cong (μ ⓓ ρ) e = dra-elim-cong ρ (dra-elim-cong μ e)
dra-β (μ ⓓ ρ) t = transᵗᵐ (dra-elim-cong ρ (dra-β μ _)) (dra-β ρ t)
dra-η (μ ⓓ ρ) t = transᵗᵐ (dra-intro-cong μ (dra-η ρ _)) (dra-η μ t)


-- The unit DRA or composition of DRAs preserve the
-- structure of closed types being natural.
dra-cong-𝟙 : {Γ : Ctx C} {T S : Ty Γ} {e : T ≅ᵗʸ S} → dra-cong 𝟙 e ≅ᵉ e
from-eq dra-cong-𝟙 = reflⁿ

dra-cong-ⓓ : {ρ : DRA C D} {μ : DRA D E} {Γ : Ctx E} {T S : Ty (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)} {e : T ≅ᵗʸ S} →
             dra-cong (μ ⓓ ρ) e ≅ᵉ dra-cong μ (dra-cong ρ e)
from-eq dra-cong-ⓓ = reflⁿ

𝟙-preserves-cl : {A : ClosedTy C} (clA : IsClosedNatural A) → dra-closed 𝟙 clA ≅ᶜᵗʸ clA
closed-natural-eq (𝟙-preserves-cl clA) σ = transᵉ reflᵗʸ-unitˡ dra-cong-𝟙

ⓓ-preserves-cl : (μ : DRA D E) (ρ : DRA C D) {A : ClosedTy C} (clA : IsClosedNatural A) →
                 dra-closed (μ ⓓ ρ) clA ≅ᶜᵗʸ dra-closed μ (dra-closed ρ clA)
closed-natural-eq (ⓓ-preserves-cl μ ρ clA) σ =
  transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ (transᵗʸ-congʳ dra-cong-ⓓ) (symᵉ (dra-cong-trans μ))))


--------------------------------------------------
-- Equivalence of modalities

record _≅ᵈ_  {C D} (μ ρ : DRA C D) : Set₁ where
  field
    eq-lock : (Γ : Ctx D) → Γ ,lock⟨ μ ⟩ ≅ᶜ Γ ,lock⟨ ρ ⟩
    eq-lock-natural-to : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) →
                         to (eq-lock Γ) ⊚ lock-fmap ρ σ ≅ˢ lock-fmap μ σ ⊚ to (eq-lock Δ)
    eq-dra-tyʳ : {Γ : Ctx D} (T : Ty (Γ ,lock⟨ μ ⟩)) → ⟨ μ ∣ T ⟩ ≅ᵗʸ ⟨ ρ ∣ T [ to (eq-lock Γ) ] ⟩

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

  eq-dra-tyˡ : {Γ : Ctx D} (T : Ty (lock ρ Γ)) → ⟨ μ ∣ T [ from (eq-lock Γ) ] ⟩ ≅ᵗʸ ⟨ ρ ∣ T ⟩
  eq-dra-tyˡ {Γ = Γ} T = begin
      ⟨ μ ∣ T [ from (eq-lock Γ) ] ⟩
    ≅⟨ eq-dra-tyʳ (T [ from (eq-lock Γ) ]) ⟩
      ⟨ ρ ∣ (T [ from (eq-lock Γ) ]) [ to (eq-lock Γ) ] ⟩
    ≅⟨ dra-cong ρ (ty-subst-seq-cong (from (eq-lock Γ) ∷ to (eq-lock Γ) ◼) (id-subst _ ◼) T (isoʳ (eq-lock Γ))) ⟩
      ⟨ ρ ∣ T [ id-subst (Γ ,lock⟨ ρ ⟩) ] ⟩
    ≅⟨ dra-cong ρ (ty-subst-id T) ⟩
      ⟨ ρ ∣ T ⟩ ∎
    where open ≅ᵗʸ-Reasoning

  eq-dra-closed : {A : ClosedTy C} → IsClosedNatural A → {Γ : Ctx D} → ⟨ μ ∣ A {Γ ,lock⟨ μ ⟩} ⟩ ≅ᵗʸ ⟨ ρ ∣ A ⟩
  eq-dra-closed {A = A} clA = begin
      ⟨ μ ∣ A ⟩
    ≅⟨ eq-dra-tyʳ A ⟩
      ⟨ ρ ∣ A [ to (eq-lock _) ] ⟩
    ≅⟨ dra-cong ρ (closed-natural clA (to (eq-lock _))) ⟩
      ⟨ ρ ∣ A ⟩ ∎
    where open ≅ᵗʸ-Reasoning

open _≅ᵈ_ public

reflᵈ : ∀ {C D} → {μ : DRA C D} → μ ≅ᵈ μ
eq-lock (reflᵈ {μ = μ}) Γ = reflᶜ
eq-lock-natural-to (reflᵈ {μ = μ}) σ = transˢ (id-subst-unitˡ _) (symˢ (id-subst-unitʳ _))
eq-dra-tyʳ (reflᵈ {μ = μ}) T = dra-cong μ (symᵗʸ (ty-subst-id T))

symᵈ : ∀ {C D} {μ ρ : DRA C D} → μ ≅ᵈ ρ → ρ ≅ᵈ μ
eq-lock (symᵈ e) Γ = symᶜ (eq-lock e Γ)
eq-lock-natural-to (symᵈ e) σ = eq-lock-natural-from e σ
eq-dra-tyʳ (symᵈ e) T = symᵗʸ (eq-dra-tyˡ e T)

transᵈ : ∀ {C D} {μ ρ κ : DRA C D} → μ ≅ᵈ ρ → ρ ≅ᵈ κ → μ ≅ᵈ κ
eq-lock (transᵈ μ=ρ ρ=κ) Γ = transᶜ (eq-lock μ=ρ Γ) (eq-lock ρ=κ Γ)
eq-lock-natural-to (transᵈ {μ = μ} {ρ} {κ} μ=ρ ρ=κ) σ = begin
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
eq-dra-tyʳ (transᵈ {μ = μ} {ρ = ρ} {κ = κ} μ=ρ ρ=κ) {Γ = Γ} T = begin
    ⟨ μ ∣ T ⟩
  ≅⟨ eq-dra-tyʳ μ=ρ T ⟩
    ⟨ ρ ∣ T [ to (eq-lock μ=ρ Γ) ] ⟩
  ≅⟨ eq-dra-tyʳ ρ=κ (T [ to (eq-lock μ=ρ Γ) ]) ⟩
    ⟨ κ ∣ (T [ to (eq-lock μ=ρ Γ) ]) [ to (eq-lock ρ=κ Γ) ] ⟩
  ≅⟨ dra-cong κ (ty-subst-comp T _ _) ⟩
    ⟨ κ ∣ T [ to (eq-lock μ=ρ Γ) ⊚ to (eq-lock ρ=κ Γ) ] ⟩ ∎
  where open ≅ᵗʸ-Reasoning

𝟙-unitʳ : (μ : DRA C D) → μ ⓓ 𝟙 ≅ᵈ μ
eq-lock (𝟙-unitʳ μ) Γ = reflᶜ
eq (eq-lock-natural-to (𝟙-unitʳ μ) σ) _ = refl
eq-dra-tyʳ (𝟙-unitʳ μ) T = symᵗʸ (dra-cong μ (ty-subst-id T))

𝟙-unitˡ : (μ : DRA C D) → 𝟙 ⓓ μ ≅ᵈ μ
eq-lock (𝟙-unitˡ μ) Γ = reflᶜ
eq (eq-lock-natural-to (𝟙-unitˡ μ) σ) _ = refl
eq-dra-tyʳ (𝟙-unitˡ μ) T = symᵗʸ (dra-cong μ (ty-subst-id T))

ⓓ-assoc : {C₁ C₂ C₃ C₄ : BaseCategory}
           (μ₃₄ : DRA C₃ C₄) (μ₂₃ : DRA C₂ C₃) (μ₁₂ : DRA C₁ C₂) →
           (μ₃₄ ⓓ μ₂₃) ⓓ μ₁₂ ≅ᵈ μ₃₄ ⓓ (μ₂₃ ⓓ μ₁₂)
eq-lock (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂) Γ = reflᶜ
eq (eq-lock-natural-to (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂) σ) _ = refl
eq-dra-tyʳ (ⓓ-assoc μ₃₄ μ₂₃ μ₁₂) T = symᵗʸ (dra-cong μ₃₄ (dra-cong μ₂₃ (dra-cong μ₁₂ (ty-subst-id T))))

ⓓ-congʳ : (ρ : DRA D E) {μ μ' : DRA C D} → μ ≅ᵈ μ' → ρ ⓓ μ ≅ᵈ ρ ⓓ μ'
eq-lock (ⓓ-congʳ ρ μ=μ') Γ = eq-lock μ=μ' (Γ ,lock⟨ ρ ⟩)
eq-lock-natural-to (ⓓ-congʳ ρ {μ} {μ'} μ=μ') σ = eq-lock-natural-to μ=μ' (lock-fmap ρ σ)
eq-dra-tyʳ (ⓓ-congʳ ρ μ=μ') T = dra-cong ρ (eq-dra-tyʳ μ=μ' T)

ⓓ-congˡ : {ρ ρ' : DRA D E} (μ : DRA C D) → ρ ≅ᵈ ρ' → ρ ⓓ μ ≅ᵈ ρ' ⓓ μ
from (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = lock-fmap μ (from (eq-lock ρ=ρ' Γ))
to (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = lock-fmap μ (to (eq-lock ρ=ρ' Γ))
isoˡ (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoˡ (eq-lock ρ=ρ' Γ))
isoʳ (eq-lock (ⓓ-congˡ μ ρ=ρ') Γ) = ctx-fmap-inverse (ctx-functor μ) (isoʳ (eq-lock ρ=ρ' Γ))
eq-lock-natural-to (ⓓ-congˡ {ρ = ρ} {ρ'} μ ρ=ρ') σ = begin
    lock-fmap μ (to (eq-lock ρ=ρ' _)) ⊚ lock-fmap μ (lock-fmap ρ' σ)
  ≅˘⟨ lock-fmap-⊚ μ _ _ ⟩
    lock-fmap μ (to (eq-lock ρ=ρ' _) ⊚ lock-fmap ρ' σ)
  ≅⟨ lock-fmap-cong μ (eq-lock-natural-to ρ=ρ' σ) ⟩
    lock-fmap μ (lock-fmap ρ σ ⊚ to (eq-lock ρ=ρ' _))
  ≅⟨ lock-fmap-⊚ μ _ _ ⟩
    lock-fmap μ (lock-fmap ρ σ) ⊚ lock-fmap μ (to (eq-lock ρ=ρ' _)) ∎
  where open ≅ˢ-Reasoning
eq-dra-tyʳ (ⓓ-congˡ {ρ = ρ} {ρ' = ρ'} μ ρ=ρ') {Γ = Γ} T = begin
    ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩
  ≅⟨ eq-dra-tyʳ ρ=ρ' ⟨ μ ∣ T ⟩ ⟩
    ⟨ ρ' ∣ ⟨ μ ∣ T ⟩ [ to (eq-lock ρ=ρ' Γ) ] ⟩
  ≅⟨ dra-cong ρ' (dra-natural μ (to (eq-lock ρ=ρ' Γ))) ⟩
    ⟨ ρ' ∣ ⟨ μ ∣ T [ lock-fmap μ (to (eq-lock ρ=ρ' Γ)) ] ⟩ ⟩ ∎
  where open ≅ᵗʸ-Reasoning

module ≅ᵈ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {μ ρ : DRA C D} → μ ≅ᵈ ρ → μ ≅ᵈ ρ
  begin_ μ=ρ = μ=ρ

  _≅⟨⟩_ : ∀ (μ {ρ} : DRA C D) → μ ≅ᵈ ρ → μ ≅ᵈ ρ
  _ ≅⟨⟩ μ=ρ = μ=ρ

  step-≅ : ∀ (μ {ρ κ} : DRA C D) → ρ ≅ᵈ κ → μ ≅ᵈ ρ → μ ≅ᵈ κ
  step-≅ _ ρ≅κ μ≅ρ = transᵈ μ≅ρ ρ≅κ

  step-≅˘ : ∀ (μ {ρ κ} : DRA C D) → ρ ≅ᵈ κ → ρ ≅ᵈ μ → μ ≅ᵈ κ
  step-≅˘ _ ρ≅κ ρ≅μ = transᵈ (symᵈ ρ≅μ) ρ≅κ

  _∎ : ∀ (μ : DRA C D) → μ ≅ᵈ μ
  _∎ _ = reflᵈ

  syntax step-≅  μ ρ≅κ μ≅ρ = μ ≅⟨  μ≅ρ ⟩ ρ≅κ
  syntax step-≅˘ μ ρ≅κ ρ≅μ = μ ≅˘⟨ ρ≅μ ⟩ ρ≅κ


--------------------------------------------------
-- Two-cells between DRAs as natural transformations
--   between the underlying context functors

-- TwoCell is defined as a record type so that Agda can better infer the two endpoint
--   modalities, e.g. in coe-ty.
record TwoCell (μ ρ : DRA C D) : Set₁ where
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
  coe t = dra-intro ρ ((dra-elim μ t) [ key-subst ]')

  coe-closed : {T : ClosedTy C} → IsClosedNatural T → {Γ : Ctx D} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
  coe-closed {T = T} clT t = ι⁻¹[ dra-cong ρ (closed-natural clT key-subst) ] coe t

open TwoCell public


-- The identity 2-cell.
id-cell : {μ : DRA C D} → TwoCell μ μ
transf id-cell = id-ctx-transf _

-- Composition of 2-cells (both vertical and horizontal)
_ⓣ-vert_ : {μ ρ κ : DRA C D} → TwoCell μ ρ → TwoCell κ μ → TwoCell κ ρ
transf (α ⓣ-vert β) = transf β ⓝ-vert transf α

_ⓣ-hor_ : {μ μ' : DRA D E} {ρ ρ' : DRA C D} → TwoCell μ μ' → TwoCell ρ ρ' → TwoCell (μ ⓓ ρ) (μ' ⓓ ρ')
transf (α ⓣ-hor β) = transf β ⓝ-hor transf α

-- An equivalence of modalities gives rise to an invertible 2-cell.
≅ᵈ-to-2-cell : {μ ρ : DRA C D} → μ ≅ᵈ ρ → TwoCell μ ρ
transf-op (transf (≅ᵈ-to-2-cell μ=ρ)) Γ = to (eq-lock μ=ρ Γ)
naturality (transf (≅ᵈ-to-2-cell μ=ρ)) = eq-lock-natural-to μ=ρ


record _≅ᵗᶜ_ {μ ρ : DRA C D} (α β : TwoCell μ ρ) : Set₁ where
  field
    key-subst-eq : ∀ {Γ} → key-subst α {Γ} ≅ˢ key-subst β
open _≅ᵗᶜ_ public

module _ {μ ρ : DRA C D} where
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

ⓣ-vert-assoc : {μ ρ κ φ : DRA C D} {α : TwoCell μ ρ} {β : TwoCell ρ κ} {γ : TwoCell κ φ} →
               (γ ⓣ-vert β) ⓣ-vert α ≅ᵗᶜ γ ⓣ-vert (β ⓣ-vert α)
key-subst-eq ⓣ-vert-assoc = symˢ ⊚-assoc

ⓣ-vert-congˡ : {μ ρ κ : DRA C D} {α α' : TwoCell ρ κ} {β : TwoCell μ ρ} →
               α ≅ᵗᶜ α' → α ⓣ-vert β ≅ᵗᶜ α' ⓣ-vert β
key-subst-eq (ⓣ-vert-congˡ e) = ⊚-congʳ (key-subst-eq e)

ⓣ-vert-congʳ : {μ ρ κ : DRA C D} {α : TwoCell ρ κ} {β β' : TwoCell μ ρ} →
               β ≅ᵗᶜ β' → α ⓣ-vert β ≅ᵗᶜ α ⓣ-vert β'
key-subst-eq (ⓣ-vert-congʳ e) = ⊚-congˡ (key-subst-eq e)

ⓣ-hor-congˡ : {μ ρ : DRA C D} {κ φ : DRA D E} {α : TwoCell μ ρ} {β β' : TwoCell κ φ} →
              β ≅ᵗᶜ β' → β ⓣ-hor α ≅ᵗᶜ β' ⓣ-hor α
key-subst-eq (ⓣ-hor-congˡ {ρ = ρ} e) = ⊚-congʳ (lock-fmap-cong ρ (key-subst-eq e))

ⓣ-hor-congʳ : {μ ρ : DRA C D} {κ φ : DRA D E} {α α' : TwoCell μ ρ} {β : TwoCell κ φ} →
              α ≅ᵗᶜ α' → β ⓣ-hor α ≅ᵗᶜ β ⓣ-hor α'
key-subst-eq (ⓣ-hor-congʳ e) = ⊚-congˡ (key-subst-eq e)

ⓣ-hor-id : {μ : DRA C D} {ρ : DRA D E} → id-cell {μ = ρ} ⓣ-hor id-cell {μ = μ} ≅ᵗᶜ id-cell
key-subst-eq (ⓣ-hor-id {μ = μ}) = transˢ (id-subst-unitˡ _) (lock-fmap-id μ)

2-cell-interchange : {μ μ' μ'' : DRA D E} {ρ ρ' ρ'' : DRA C D}
                     {α : TwoCell μ μ'} {β : TwoCell μ' μ''} {γ : TwoCell ρ ρ'} {δ : TwoCell ρ' ρ''} →
                     (β ⓣ-vert α) ⓣ-hor (δ ⓣ-vert γ) ≅ᵗᶜ (β ⓣ-hor δ) ⓣ-vert (α ⓣ-hor γ)
key-subst-eq (2-cell-interchange {ρ'' = ρ''} {δ = δ}) =
  transˢ (⊚-congʳ (lock-fmap-⊚ ρ'' _ _)) (
  transˢ ⊚-assoc (
  transˢ (⊚-congʳ (transˢ (symˢ ⊚-assoc) (⊚-congˡ (naturality (transf δ) _)))) (
  transˢ (⊚-congʳ ⊚-assoc) (
  symˢ ⊚-assoc))))

ⓣ-hor-unitˡ : {μ ρ : DRA C D} {α : TwoCell μ ρ} →
              ≅ᵈ-to-2-cell (𝟙-unitˡ ρ) ⓣ-vert (id-cell {μ = 𝟙} ⓣ-hor α) ≅ᵗᶜ α ⓣ-vert ≅ᵈ-to-2-cell (𝟙-unitˡ μ)
key-subst-eq (ⓣ-hor-unitˡ {ρ = ρ}) =
  transˢ (id-subst-unitʳ _) (transˢ (⊚-congʳ (lock-fmap-id ρ)) (transˢ (id-subst-unitʳ _) (symˢ (id-subst-unitˡ _))))

ⓣ-hor-unitʳ : {μ ρ : DRA C D} {α : TwoCell μ ρ} →
              ≅ᵈ-to-2-cell (𝟙-unitʳ ρ) ⓣ-vert (α ⓣ-hor id-cell {μ = 𝟙}) ≅ᵗᶜ α ⓣ-vert ≅ᵈ-to-2-cell (𝟙-unitʳ μ)
key-subst-eq (ⓣ-hor-unitʳ {ρ = ρ}) = id-subst-unitʳ _

ⓣ-hor-assoc : {F : BaseCategory}
              {μ μ' : DRA C D} {ρ ρ' : DRA D E} {κ κ' : DRA E F}
              {α : TwoCell μ μ'} {β : TwoCell ρ ρ'} {γ : TwoCell κ κ'} →
              ≅ᵈ-to-2-cell (ⓓ-assoc _ _ _) ⓣ-vert ((γ ⓣ-hor β) ⓣ-hor α) ≅ᵗᶜ (γ ⓣ-hor (β ⓣ-hor α)) ⓣ-vert ≅ᵈ-to-2-cell (ⓓ-assoc _ _ _)
key-subst-eq (ⓣ-hor-assoc {μ' = μ'}) =
  transˢ (id-subst-unitʳ _) (transˢ (⊚-congʳ (lock-fmap-⊚ μ' _ _)) (transˢ (symˢ ⊚-assoc) (symˢ (id-subst-unitˡ _))))
