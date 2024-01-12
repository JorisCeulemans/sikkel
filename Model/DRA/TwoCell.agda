--------------------------------------------------
-- Two-cells between DRAs
--------------------------------------------------

module Model.DRA.TwoCell where

open import Data.Product renaming (_,_ to [_,_])
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.Reasoning.Syntax
open import Preliminaries

open import Model.DRA.Basics

open import Model.BaseCategory
open import Model.CwF-Structure

private
  variable
    C D E : BaseCategory

infix 1 _≅ᵗᶜ_
infixl 20 _ⓣ-vert_ _ⓣ-hor_


--------------------------------------------------
-- Definition of a two-cell as a natural transformations between the underlying context functors

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

  coe : {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T [ key-subst ] ⟩
  coe t = dra-intro ρ ((dra-elim μ t) [ key-subst ]')

  coe-closed : {T : ClosedTy C} → IsClosedNatural T → {Γ : Ctx D} → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
  coe-closed {T = T} clT t = ι⁻¹[ dra-cong ρ (closed-natural clT key-subst) ] coe t

open TwoCell public


-- The identity 2-cell
id-cell : {μ : DRA C D} → TwoCell μ μ
transf id-cell = id-ctx-transf _

-- Composition of 2-cells (both vertical and horizontal)
_ⓣ-vert_ : {μ ρ κ : DRA C D} → TwoCell μ ρ → TwoCell κ μ → TwoCell κ ρ
transf (α ⓣ-vert β) = transf β ⓝ-vert transf α

_ⓣ-hor_ : {μ μ' : DRA D E} {ρ ρ' : DRA C D} → TwoCell μ μ' → TwoCell ρ ρ' → TwoCell (μ ⓓ ρ) (μ' ⓓ ρ')
transf (α ⓣ-hor β) = transf β ⓝ-hor transf α


--------------------------------------------------
-- A two-cell α from μ to ρ introduces a natural transformation
--   from ⟨ μ ∣ _ ⟩ to ⟨ ρ ∣ _ [ key-subst α ] ⟩ (both seen as functors from
--   Ty (Γ ,lock⟨ μ ⟩) to Ty Γ.

coe-tm-helper : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} {A : Ty Γ} →
                Tm (Γ ,, A) (⟨ μ ∣ T ⟩ [ π ]) → Tm (Γ ,, A) (⟨ ρ ∣ T [ key-subst α ] ⟩ [ π ])
coe-tm-helper {μ = μ} {ρ} α {Γ} {T} t =
  ι[ dra-natural ρ π ] (dra-intro ρ (ι[ ty-subst-cong-subst-2-2 T (key-subst-natural α) ] (
      (dra-elim μ (ι⁻¹[ dra-natural μ π ] t))
    [ key-subst α ]')))

coe-tm : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} →
         Tm (Γ ,, ⟨ μ ∣ T ⟩) (⟨ ρ ∣ T [ key-subst α ] ⟩ [ π ])
coe-tm {μ = μ} {ρ} α {Γ} {T} = coe-tm-helper α ξ

coe-trans : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} →
            ⟨ μ ∣ T ⟩ ↣ ⟨ ρ ∣ T [ key-subst α ] ⟩
func (coe-trans α) t = coe-tm α ⟨ _ , [ _ , t ] ⟩'
naturality (coe-trans α) {eγ = refl} = naturality (coe-tm α) _ refl

coe-tm-helper-cong : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} {A : Ty Γ} →
                     {t t' : Tm (Γ ,, A) (⟨ μ ∣ T ⟩ [ π ])} →
                     t ≅ᵗᵐ t' → coe-tm-helper α t ≅ᵗᵐ coe-tm-helper α t'
coe-tm-helper-cong {μ = μ} {ρ} α et = ι-cong (dra-intro-cong ρ (ι-cong (tm-subst-cong-tm _ (dra-elim-cong μ (ι⁻¹-cong et)))))

coe-tm-helper-convert : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T S : Ty (Γ ,lock⟨ μ ⟩)} {A : Ty Γ}
                        (φ : T ↣ S) {t : Tm (Γ ,, A) (⟨ μ ∣ T ⟩ [ π ])} →
                        convert-tm (ty-subst-map π (dra-map ρ (ty-subst-map _ φ))) (coe-tm-helper α t)
                          ≅ᵗᵐ
                        coe-tm-helper α (convert-tm (ty-subst-map π (dra-map μ φ)) t)
coe-tm-helper-convert {μ = μ} {ρ} α φ =
  transᵗᵐ (convert-tm-ι-2-2 {e' = dra-natural ρ π} (symⁿ (dra-natural-map-to ρ π _))) (ι-cong (
  transᵗᵐ (dra-intro-convert ρ _) (dra-intro-cong ρ (
  transᵗᵐ (convert-tm-ι-2-2 (symⁿ (ty-subst-cong-subst-2-2-natural-to φ _))) (ι-cong (
  transᵗᵐ convert-tm-subst-commute (tm-subst-cong-tm _ (
  transᵗᵐ (dra-elim-convert μ _) (dra-elim-cong μ (
  convert-tm-ι-2-2 (dra-natural-map μ π φ))
  )))))))))

coe-tm-helper-subst : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} {A B : Ty Γ}
                      {t : Tm (Γ ,, B) (⟨ μ ∣ T ⟩ [ π ])} (b : Tm (Γ ,, A) (B [ π ])) →
                      ι⁻¹[ ty-subst-cong-subst-2-1 _ (ctx-ext-subst-β₁ π b) ] ((coe-tm-helper α t) [ π ∷ˢ b ]')
                        ≅ᵗᵐ
                      coe-tm-helper α (ι⁻¹[ ty-subst-cong-subst-2-1 _ (ctx-ext-subst-β₁ π b) ] (t [ π ∷ˢ b ]'))
coe-tm-helper-subst {C = C} {μ = μ} {ρ} α {Γ} {T} b =
  transᵗᵐ (ι⁻¹-cong (symᵗᵐ ι-subst-commute)) (
  transᵗᵐ (ι-congᵉ-2-2 (move-symᵗʸ-out (symᵉ (dra-natural-ty-subst-2-1 ρ _)))) (ι-cong (
  transᵗᵐ (ι⁻¹-cong (dra-intro-natural ρ _ _)) (
    transᵗᵐ (ι-congᵉ-2-1 (transᵉ (transᵗʸ-congˡ symᵗʸ-transᵗʸ) (transᵉ transᵗʸ-assoc transᵗʸ-cancelʳ-symˡ))) (transᵗᵐ (ι-congᵉ (symᵉ (dra-cong-sym ρ))) (
  transᵗᵐ (dra-intro-ι ρ _) (dra-intro-cong ρ (
  transᵗᵐ (ι⁻¹-cong (symᵗᵐ ι-subst-commute)) (
  transᵗᵐ (ι-congᵉ-2-2 lemma) (ι-cong (
  transᵗᵐ (ι-cong (tm-subst-cong-subst-2-2 _ (key-subst-natural α))) (
    transᵗᵐ (ι-congᵉ-2-1 (transᵉ transᵗʸ-assoc transᵗʸ-cancelʳ-symˡ)) (
  transᵗᵐ ι⁻¹-subst-commute (tm-subst-cong-tm _ (
  transᵗᵐ (ι⁻¹-cong (dra-elim-natural μ _ _)) (
  transᵗᵐ (dra-elim-ι μ _) (dra-elim-cong μ (
  transᵗᵐ (ι-cong (ι⁻¹-cong (symᵗᵐ ι⁻¹-subst-commute))) (
  transᵗᵐ (symᵗᵐ ι-trans) (ι-congᵉ-2-2 (
    transᵉ (transᵗʸ-congˡ (transᵗʸ-congˡ (dra-cong-sym μ))) (transᵉ (transᵗʸ-congˡ (symᵉ symᵗʸ-transᵗʸ)) (
    transᵉ (symᵉ symᵗʸ-transᵗʸ) (transᵉ (symᵗʸ-cong (symᵉ (dra-natural-ty-subst-2-1 μ _))) symᵗʸ-transᵗʸ))))))))))))))))))))))))
  where
    open BaseCategory C
    lemma : _ ≅ᵉ transᵗʸ (ty-subst-cong-subst-2-2 T (key-subst-natural α))
                         (transᵗʸ (symᵗʸ (ty-subst-cong-ty _ (ty-subst-cong-subst-2-1 T (ctx-fmap-cong-2-1 (ctx-functor μ) (ctx-ext-subst-β₁ π b)))))
                                  (symᵗʸ (ty-subst-cong-subst-2-2 _ (key-subst-natural α))))
    eq (from-eq lemma) _ = trans (sym (ty-comp T)) (trans (ty-cong T (trans hom-idʳ (sym (trans hom-idˡ hom-idʳ)))) (trans (ty-comp T) (ty-comp T)))

coe-tm-helper-ⓣ : {μ ρ κ : DRA C D} (α : TwoCell μ ρ) (β : TwoCell ρ κ) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)}
                  {A : Ty Γ} {t : Tm (Γ ,, A) (⟨ μ ∣ T ⟩ [ π ])} →
                  coe-tm-helper β (coe-tm-helper α t)
                    ≅ᵗᵐ
                  ι[ ty-subst-cong-ty π (dra-cong κ (ty-subst-comp T _ _)) ] (coe-tm-helper (β ⓣ-vert α) t)
coe-tm-helper-ⓣ {C} {μ = μ} {ρ} {κ} α β {Γ} {T} =
  transᵗᵐ (ι-cong (dra-intro-cong κ (ι-cong (tm-subst-cong-tm _ (transᵗᵐ (dra-elim-cong ρ ι-symˡ) (dra-β ρ _)))))) (
  transᵗᵐ (ι-cong (dra-intro-cong κ (ι-cong (symᵗᵐ ι-subst-commute)))) (
  transᵗᵐ (ι-cong (dra-intro-cong κ (transᵗᵐ (symᵗᵐ ι-trans) (ι-cong (tm-subst-comp _ _ _))))) (
  transᵗᵐ (ι-cong (dra-intro-cong κ (ι-congᵉ-2-2 lemma))) (
  transᵗᵐ (ι-cong (symᵗᵐ (dra-intro-ι κ _))) (ι-congᵉ-2-2 (dra-natural-ty-eq κ π _))))))
  where
    open BaseCategory C
    lemma : _ ≅ᵉ transᵗʸ (ty-subst-cong-ty _ (ty-subst-comp _ _ _)) (ty-subst-cong-subst-2-2 _ (key-subst-natural (β ⓣ-vert α)))
    eq (from-eq lemma) t = trans (sym (ty-comp T)) (ty-cong T hom-idˡ)


coe-tm-natural : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T S : Ty (Γ ,lock⟨ μ ⟩)}
                 (φ : T ↣ S) →
                 convert-tm (ty-subst-map π (dra-map ρ (ty-subst-map _ φ))) (coe-tm α)
                   ≅ᵗᵐ
                 ι⁻¹[ ty-subst-cong-subst-2-1 _ (,,-map-π _) ] (coe-tm α [ ,,-map (dra-map μ φ) ]')
coe-tm-natural {μ = μ} {ρ} α φ =
  transᵗᵐ (coe-tm-helper-convert α φ) (transᵗᵐ (coe-tm-helper-cong α (ξ-convert _)) (symᵗᵐ (coe-tm-helper-subst α _)))

coe-trans-natural : {μ ρ : DRA C D} (α : TwoCell μ ρ) {Γ : Ctx D} {T S : Ty (Γ ,lock⟨ μ ⟩)}
                    (φ : T ↣ S) →
                    dra-map ρ (ty-subst-map (key-subst α) φ) ⊙ coe-trans α ≅ⁿ coe-trans α ⊙ dra-map μ φ
eq (coe-trans-natural {ρ = ρ} α {S = S} φ) t = trans (eq (coe-tm-natural α φ) _) (strong-ty-id ⟨ ρ ∣ S [ key-subst α ] ⟩)

coe-tm-id : (μ : DRA C D) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} →
            coe-tm {μ = μ} id-cell ≅ᵗᵐ ι[ ty-subst-cong-ty π (dra-cong μ (ty-subst-id T)) ] ξ
coe-tm-id μ =
  transᵗᵐ (ι-cong (dra-intro-cong μ (ι-cong (tm-subst-id _)))) (
  transᵗᵐ (ι-cong (dra-intro-cong μ (ι-congᵉ-2-1 (ty-subst-cong-subst-2-2-id _)))) (
  transᵗᵐ (ι-cong (dra-intro-cong μ (dra-elim-ι μ _))) (
  transᵗᵐ (ι-cong (dra-η μ _)) (
  transᵗᵐ (ι-congᵉ-2-2 (dra-natural-ty-eq μ π (ty-subst-id _))) (
  ι-cong ι-symʳ)))))

coe-trans-id : (μ : DRA C D) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} →
               coe-trans {μ = μ} id-cell ≅ⁿ dra-map μ (ty-subst-id-to T)
eq (coe-trans-id μ) t = eq (coe-tm-id μ) [ _ , t ]

coe-tm-ⓣ : {μ ρ κ : DRA C D} {α : TwoCell μ ρ} {β : TwoCell ρ κ} {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} →
           coe-tm (β ⓣ-vert α)
             ≅ᵗᵐ
           ι⁻¹[ ty-subst-cong-ty _ (dra-cong κ (ty-subst-comp T _ _)) ] ι⁻¹[ ty-subst-cong-subst-2-1 _ (ctx-ext-subst-β₁ _ _) ]
                (coe-tm β [ π ∷ˢ coe-tm α ]')
coe-tm-ⓣ {α = α} {β} = symᵗᵐ (
  transᵗᵐ (ι⁻¹-cong (coe-tm-helper-subst β _)) (move-ι⁻¹-left (
  transᵗᵐ (coe-tm-helper-cong β (move-ι⁻¹-left (ctx-ext-subst-β₂ π _))) (
  coe-tm-helper-ⓣ α β))))

coe-trans-ⓣ : {μ ρ κ : DRA C D} {α : TwoCell μ ρ} {β : TwoCell ρ κ} {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)} →
              coe-trans (β ⓣ-vert α) ≅ⁿ dra-map κ (ty-subst-comp-from T _ _) ⊙ coe-trans β ⊙ coe-trans α
eq (coe-trans-ⓣ {κ = κ} {α} {β}) t =
  trans (eq (coe-tm-ⓣ {α = α} {β}) [ _ , t ]) (cong (func (dra-map κ _)) (strong-ty-id ⟨ κ ∣ _ ⟩))


--------------------------------------------------
-- Equivalence of two-cells (i.e. equivalence of the underlying natural transformations)

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

module ≅ᵗᶜ-Reasoning {C D} {μ ρ : DRA C D} where
  open begin-syntax {A = TwoCell μ ρ} _≅ᵗᶜ_ id public
  open ≅-syntax {A = TwoCell μ ρ} _≅ᵗᶜ_ _≅ᵗᶜ_ transᵗᶜ symᵗᶜ public
  open end-syntax {A = TwoCell μ ρ} _≅ᵗᶜ_ reflᵗᶜ public


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
    transˢ (⊚-congʳ ⊚-assoc) (symˢ ⊚-assoc))))

-- In order to express that ⓣ-hor is associative and that id-cell is a
-- unit for ⓣ-hor, we need the associator and unitor in the 2-category
-- of base categories, DRAs and 2-cells. These proofs are therefore
-- included in Model.DRA.Equivalence.


coe-tm-cong : {μ ρ : DRA C D} {α β : TwoCell μ ρ} {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)}
              (ℯ : α ≅ᵗᶜ β) →
              ι⁻¹[ ty-subst-cong-ty π (dra-cong ρ (ty-subst-cong-subst (key-subst-eq ℯ) T)) ] coe-tm α ≅ᵗᵐ coe-tm β
coe-tm-cong {μ = μ} {ρ} {T = T} ℯ = move-ι⁻¹-left (symᵗᵐ (
  transᵗᵐ (ι-congᵉ-2-2 (symᵉ (dra-natural-ty-eq ρ _ _))) (ι-cong (
  transᵗᵐ (dra-intro-ι ρ _) (dra-intro-cong ρ (
  transᵗᵐ (ι-congᵉ-2-2 lemma) (ι-cong (
  symᵗᵐ (tm-subst-cong-subst _ (key-subst-eq ℯ))))))))))
  where
    lemma : _ ≅ᵉ _
    eq (from-eq lemma) _ = trans (sym (ty-comp T)) (trans (ty-cong T refl) (ty-comp T))

coe-trans-cong : {μ ρ : DRA C D} {α β : TwoCell μ ρ} {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)}
                 (ℯ : α ≅ᵗᶜ β) →
                 dra-map ρ (ty-subst-eq-subst-morph (key-subst-eq ℯ) T) ⊙ coe-trans α ≅ⁿ coe-trans β
eq (coe-trans-cong ℯ) t = eq (coe-tm-cong ℯ) _
