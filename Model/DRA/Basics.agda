--------------------------------------------------
-- Definition and basic functions regarding dependent adjunctions
--------------------------------------------------

module Model.DRA.Basics where

open import Model.BaseCategory
open import Model.CwF-Structure

private
  variable
    C D E : BaseCategory

infixl 20 _ⓓ_


--------------------------------------------------
-- Definition of a DRA (dependent right adjoint)
--   Note that what we define here is actually a dependent adjunction,
--   which consists of a context functor and a dependent right
--   adjoint. We use however the more or less standard abbreviation
--   DRA as the name to use in Sikkel.

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

    -- We can push substitutions under the modal type former but this
    -- will apply a lock to them. Again, this must happen in a
    -- coherent way (i.e. the modal type former is a pseudonatural
    -- transformation from the pseudofunctor Ty ∘ lock to Ty).
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

    -- Term formers coming with a DRA and their laws.
    dra-intro : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm (lock Γ) T → Tm Γ (⟨_∣_⟩ T)
    dra-intro-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm (lock Γ) T} →
                     t ≅ᵗᵐ t' → dra-intro t ≅ᵗᵐ dra-intro t'
    dra-intro-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
                        (dra-intro t) [ σ ]' ≅ᵗᵐ ι[ dra-natural σ ] dra-intro (t [ lock-fmap σ ]')
    dra-intro-convert : {Γ : Ctx D} {T S : Ty (lock Γ)} {η : T ↣ S} (t : Tm (lock Γ) T) →
                        convert-tm (dra-map η) (dra-intro t) ≅ᵗᵐ dra-intro (convert-tm η t)

    dra-elim : {Γ : Ctx D} {T : Ty (lock Γ)} → Tm Γ (⟨_∣_⟩ T) → Tm (lock Γ) T
    dra-elim-cong : {Γ : Ctx D} {T : Ty (lock Γ)} {t t' : Tm Γ (⟨_∣_⟩ T)} →
                    t ≅ᵗᵐ t' → dra-elim t ≅ᵗᵐ dra-elim t'
    -- Naturality of dra-elim and the fact that it commutes with convert-tm can be proved
    -- from dra-intro-natural, dra-intro-convert and the β and η laws (see below).

    dra-β : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm (lock Γ) T) →
            dra-elim (dra-intro t) ≅ᵗᵐ t
    dra-η : {Γ : Ctx D} {T : Ty (lock Γ)} (t : Tm Γ (⟨_∣_⟩ T)) →
            dra-intro (dra-elim t) ≅ᵗᵐ t

open DRA public
_,lock⟨_⟩ : Ctx D → DRA C D → Ctx C
Γ ,lock⟨ μ ⟩ = lock μ Γ


--------------------------------------------------
-- Some properties derived from the definition of a DRA

module _ (μ : DRA C D) where
  dra-natural-map-to : {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T S : Ty (lock μ Δ)} (η : T ↣ S) →
                       to (dra-natural μ σ) ⊙ dra-map μ (ty-subst-map (lock-fmap μ σ) η)
                         ≅ⁿ
                       ty-subst-map σ (dra-map μ η) ⊙ to (dra-natural μ σ {T = T})
  dra-natural-map-to σ η = exchange-from-to-out (dra-natural μ σ) (dra-natural μ σ) (dra-natural-map μ σ η)

  dra-map-cong-2-0 : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {φ : T ↣ S} {η : S ↣ T} →
                     η ⊙ φ ≅ⁿ id-trans T →
                     dra-map μ η ⊙ dra-map μ φ ≅ⁿ id-trans ⟨ μ ∣ T ⟩
  dra-map-cong-2-0 𝔢 = transⁿ (symⁿ (dra-map-⊙ μ)) (transⁿ (dra-map-cong μ 𝔢) (dra-map-id μ))

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

  dra-natural-ty-subst-2-1 : {Γ Δ Θ : Ctx D} {σ : Γ ⇒ Δ} {σ' : Δ ⇒ Θ} {τ : Γ ⇒ Θ} (ε : σ' ⊚ σ ≅ˢ τ)
                             {T : Ty (Θ ,lock⟨ μ ⟩)} →
                             transᵗʸ (ty-subst-cong-subst-2-1 ⟨ μ ∣ T ⟩ ε) (
                             dra-natural μ τ)
                               ≅ᵉ
                             transᵗʸ (ty-subst-cong-ty σ (dra-natural μ σ')) (
                             transᵗʸ (dra-natural μ σ) (
                             dra-cong (ty-subst-cong-subst-2-1 T (ctx-fmap-cong-2-1 (ctx-functor μ) ε))))
  dra-natural-ty-subst-2-1 ε =
      transᵉ transᵗʸ-assoc (
    transᵉ (transᵗʸ-congʳ (dra-natural-subst-eq ε)) (
    transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ (dra-cong-cong (transᵉ (symᵉ transᵗʸ-cancelˡ-symʳ) transᵗʸ-assoc)))) (
      transᵉ (transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ dra-cong-trans)) (transᵉ (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc)) (symᵉ transᵗʸ-assoc))) (
    transᵉ (transᵗʸ-congˡ (symᵉ (dra-natural-⊚ _ _))) (
      transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ transᵗʸ-assoc)) (
    transᵗʸ-congʳ (transᵗʸ-congʳ (transᵉ (symᵉ dra-cong-trans) (dra-cong-cong (transᵗʸ-congʳ (
                  transᵉ (transᵗʸ-congˡ (symᵉ ty-subst-cong-subst-sym)) (symᵉ ty-subst-cong-subst-trans))))))))))))


  dra-intro-ι : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {T=S : T ≅ᵗʸ S} (t : Tm (lock μ Γ) S) →
                ι[ dra-cong T=S ] (dra-intro μ t) ≅ᵗᵐ dra-intro μ (ι[ T=S ] t)
  dra-intro-ι t = transᵗᵐ ι-convert (transᵗᵐ (dra-intro-convert μ t) (dra-intro-cong μ (symᵗᵐ ι-convert)))

  dra-elim-natural : {Δ Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty (lock μ Γ)} (t : Tm Γ ⟨ μ ∣ T ⟩) →
                     (dra-elim μ t) [ lock-fmap μ σ ]' ≅ᵗᵐ dra-elim μ (ι⁻¹[ dra-natural μ σ ] (t [ σ ]'))
  dra-elim-natural σ t = begin
      (dra-elim μ t) [ lock-fmap μ σ ]'
    ≅⟨ dra-β μ _ ⟨
      dra-elim μ (dra-intro μ ((dra-elim μ t) [ lock-fmap μ σ ]'))
    ≅⟨ dra-elim-cong μ ι-symˡ ⟨
      dra-elim μ (ι⁻¹[ dra-natural μ σ ] (ι[ dra-natural μ σ ] (dra-intro μ ((dra-elim μ t) [ lock-fmap μ σ ]'))))
    ≅⟨ dra-elim-cong μ (ι⁻¹-cong (dra-intro-natural μ σ (dra-elim μ t))) ⟨
      dra-elim μ (ι⁻¹[ dra-natural μ σ ] (dra-intro μ (dra-elim μ t) [ σ ]'))
    ≅⟨ dra-elim-cong μ (ι⁻¹-cong (tm-subst-cong-tm σ (dra-η μ t))) ⟩
      dra-elim μ (ι⁻¹[ dra-natural μ σ ] (t [ σ ]')) ∎
    where open ≅ᵗᵐ-Reasoning

  dra-elim-convert : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {φ : T ↣ S} (t : Tm Γ ⟨ μ ∣ T ⟩) →
                     convert-tm φ (dra-elim μ t) ≅ᵗᵐ dra-elim μ (convert-tm (dra-map μ φ) t)
  dra-elim-convert t =
    transᵗᵐ (symᵗᵐ (dra-β μ _)) (dra-elim-cong μ (transᵗᵐ (symᵗᵐ (dra-intro-convert μ _)) (convert-tm-cong-tm (dra-η μ t))))

  dra-elim-ι : {Γ : Ctx D} {T S : Ty (lock μ Γ)} {T=S : T ≅ᵗʸ S} (t : Tm Γ ⟨ μ ∣ S ⟩) →
               ι[ T=S ] (dra-elim μ t) ≅ᵗᵐ dra-elim μ (ι[ dra-cong T=S ] t)
  dra-elim-ι {T = T} {S = S} {T=S = T=S} t = begin
      ι[ T=S ] dra-elim μ t
    ≅⟨ dra-β μ _ ⟨
      dra-elim μ (dra-intro μ (ι[ T=S ] dra-elim μ t))
    ≅⟨ dra-elim-cong μ (dra-intro-ι _) ⟨
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
      transᵉ (transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-trans) (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc))) )(
    transᵉ (transᵗʸ-congʳ (transᵗʸ-congˡ (symᵉ (dra-natural-ty-eq μ σ _)))) (
      transᵉ (transᵉ (transᵗʸ-congʳ transᵗʸ-assoc) (symᵉ transᵗʸ-assoc)) (
    transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans μ)) (transᵉ (dra-cong-cong μ (closed-⊚ clT _ _)) (dra-cong-trans μ)))) (
      transᵉ (transᵉ (symᵉ transᵗʸ-assoc) (transᵗʸ-congˡ transᵗʸ-assoc)) (
    transᵉ (transᵗʸ-congˡ (dra-natural-⊚ μ τ σ)) (
      transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ transᵗʸ-assoc)) (
    transᵗʸ-congʳ (transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans μ)) (dra-cong-cong μ (closed-subst-eq clT (lock-fmap-⊚ μ τ σ))))))))))))
  IsClosedNatural.closed-subst-eq dra-closed ε =
      transᵉ (symᵉ transᵗʸ-assoc) (
    transᵉ (transᵗʸ-congˡ (dra-natural-subst-eq μ ε)) (
      transᵉ transᵗʸ-assoc (
    transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans μ)) (dra-cong-cong μ (closed-subst-eq clT (lock-fmap-cong μ ε)))))))

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
  ≅⟨ ι-cong (dra-intro-ι μ _) ⟨
    ι[ dra-natural μ σ ] (ι[ dra-cong μ (dra-natural ρ _) ] dra-intro μ (dra-intro ρ (t [ lock-fmap ρ (lock-fmap μ σ) ]')))
  ≅⟨ ι-trans ⟨
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
