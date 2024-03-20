--------------------------------------------------
-- Closed types (i.e. types that can be defined in any context)
--------------------------------------------------

module Model.CwF-Structure.ClosedType where

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term
open import Model.CwF-Structure.ContextExtension
open import Model.CwF-Structure.ContextEquivalence

private
  variable
    C : BaseCategory
    Γ Δ Θ : Ctx C

infix 1 _≅ᶜⁿ_ _≅ᶜᵗʸ_


--------------------------------------------------
-- Definition of closed types

ClosedTy : BaseCategory → Set₁
ClosedTy C = {Γ : Ctx C} → Ty Γ

-- A "genuine" closed type should be natural.
-- I.e. it is a pseudonatural transformation from the terminal
-- pseudofunctor (from Ctx to Groupoids) to the pseudofunctor Ty.
record IsClosedNatural {C} (U : ClosedTy C) : Set₁ where
  no-eta-equality
  field
    closed-natural : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) →
                     U [ σ ] ≅ᵗʸ U
    closed-id : {Γ : Ctx C} → closed-natural (id-subst Γ) ≅ᵉ ty-subst-id U
    closed-⊚ : {Γ Δ Θ : Ctx C} (σ : Δ ⇒ Θ) (τ : Γ ⇒ Δ) →
               (transᵗʸ (ty-subst-cong-ty τ (closed-natural σ)) (closed-natural τ))
                 ≅ᵉ
               (transᵗʸ (ty-subst-comp U σ τ) (closed-natural (σ ⊚ τ)))
    closed-subst-eq : {Γ Δ : Ctx C} {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) →
                      transᵗʸ (ty-subst-cong-subst ε U) (closed-natural τ) ≅ᵉ closed-natural σ

open IsClosedNatural public

closed-substs-eq-2-2 : {Γ Δ Θ1 Θ2 : Ctx C} {σ1 : Θ1 ⇒ Δ} {τ1 : Γ ⇒ Θ1} {σ2 : Θ2 ⇒ Δ} {τ2 : Γ ⇒ Θ2} →
                       {A : ClosedTy C} (clA : IsClosedNatural A) (ε : σ1 ⊚ τ1 ≅ˢ σ2 ⊚ τ2) →
                       transᵗʸ (ty-subst-cong-ty τ1 (closed-natural clA σ1)) (closed-natural clA τ1)
                         ≅ᵉ
                       transᵗʸ (ty-subst-cong-subst-2-2 A ε) (transᵗʸ (ty-subst-cong-ty τ2 (closed-natural clA σ2)) (closed-natural clA τ2))
closed-substs-eq-2-2 clA ε =
  transᵉ (closed-⊚ clA _ _) (
  transᵉ (transᵗʸ-congʳ (symᵉ (closed-subst-eq clA ε))) (
  transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ (symᵉ transᵗʸ-cancelˡ-symˡ))) (
  transᵉ (transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ transᵗʸ-assoc) (transᵉ (transᵗʸ-congˡ (symᵉ transᵗʸ-assoc)) transᵗʸ-assoc))) (symᵉ transᵗʸ-assoc)) (
  transᵗʸ-congʳ (symᵉ (closed-⊚ clA _ _))))))

closed-substs-eq-2-1 : {Γ Δ Θ : Ctx C} {σ1 : Δ ⇒ Θ} {σ2 : Γ ⇒ Δ} {τ : Γ ⇒ Θ} →
                       {A : ClosedTy C} (clA : IsClosedNatural A) (ε : σ1 ⊚ σ2 ≅ˢ τ) →
                       transᵗʸ (ty-subst-cong-ty σ2 (closed-natural clA σ1)) (closed-natural clA σ2)
                         ≅ᵉ
                       transᵗʸ (ty-subst-cong-subst-2-1 A ε) (closed-natural clA τ)
closed-substs-eq-2-1 clA ε =
  transᵉ (closed-⊚ clA _ _) (
  transᵉ (transᵗʸ-congʳ (symᵉ (closed-subst-eq clA ε)))
  (symᵉ transᵗʸ-assoc))


--------------------------------------------------
-- A type in the empty context gives rise to a closed type.

From-◇-ty : Ty {C = C} ◇ → ClosedTy C
From-◇-ty T {Γ = Γ} = T [ !◇ Γ ]

From-◇-ty-natural : (T : Ty {C = C} ◇) → IsClosedNatural (From-◇-ty T)
IsClosedNatural.closed-natural (From-◇-ty-natural T) σ = transᵗʸ (ty-subst-comp T _ σ) (ty-subst-cong-subst (◇-terminal _ _ _) T)
eq (from-eq (IsClosedNatural.closed-id (From-◇-ty-natural T))) _ = ty-id T
eq (from-eq (IsClosedNatural.closed-⊚ (From-◇-ty-natural {C} T) σ τ)) _ = ty-cong-2-1 T (BaseCategory.hom-idʳ C)
eq (from-eq (IsClosedNatural.closed-subst-eq (From-◇-ty-natural {C} T) ε)) _ = ty-cong-2-1 T (BaseCategory.hom-idʳ C)


--------------------------------------------------
-- A better version of substitution for terms of closed types, in
-- which no substitution is applied to the type.

_[_∣_]cl : {T : ClosedTy C} → Tm Δ T → IsClosedNatural T → (Γ ⇒ Δ) → Tm Γ T
t [ clT ∣ σ ]cl = ι⁻¹[ closed-natural clT σ ] (t [ σ ]')

module _ {T : ClosedTy C} (clT : IsClosedNatural T) where
  cl-tm-subst-id : (t : Tm Γ T) → t [ clT ∣ id-subst Γ ]cl ≅ᵗᵐ t
  cl-tm-subst-id t =
    begin
      ι⁻¹[ closed-natural clT (id-subst _) ] (t [ id-subst _ ]')
    ≅⟨ ι⁻¹-cong (tm-subst-id t) ⟩
      ι⁻¹[ closed-natural clT (id-subst _) ] (ι[ ty-subst-id T ] t)
    ≅⟨ ι-congᵉ-2-1 (transᵉ (transᵗʸ-congˡ (symᵗʸ-cong (closed-id clT))) symᵗʸ-invˡ) ⟩
      ι[ reflᵗʸ ] t
    ≅⟨ ι-refl ⟩
      t ∎
    where open ≅ᵗᵐ-Reasoning

  cl-tm-subst-⊚ : {τ : Δ ⇒ Θ} {σ : Γ ⇒ Δ} (t : Tm Θ T) →
                  (t [ clT ∣ τ ]cl) [ clT ∣ σ ]cl ≅ᵗᵐ t [ clT ∣ τ ⊚ σ ]cl
  cl-tm-subst-⊚ {τ = τ} {σ} t =
    begin
      ι⁻¹[ closed-natural clT σ ] ((ι⁻¹[ closed-natural clT τ ] (t [ τ ]')) [ σ ]')
    ≅⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟨
      ι⁻¹[ closed-natural clT σ ] (ι⁻¹[ ty-subst-cong-ty σ (closed-natural clT τ) ] ((t [ τ ]') [ σ ]'))
    ≅⟨ ι⁻¹-cong (ι⁻¹-cong (tm-subst-comp t τ σ)) ⟩
      ι⁻¹[ closed-natural clT σ ] (ι⁻¹[ ty-subst-cong-ty σ (closed-natural clT τ) ] (ι[ ty-subst-comp T τ σ ] (t [ τ ⊚ σ ]')))
    ≅⟨ ι⁻¹-congᵉ-2-2 (closed-⊚ clT τ σ) ⟩
      ι⁻¹[ closed-natural clT (τ ⊚ σ) ] (ι⁻¹[ ty-subst-comp T τ σ ] (ι[ ty-subst-comp T τ σ ] (t [ τ ⊚ σ ]')))
    ≅⟨ ι⁻¹-cong ι-symˡ ⟩
      ι⁻¹[ closed-natural clT (τ ⊚ σ) ] (t [ τ ⊚ σ ]') ∎
    where open ≅ᵗᵐ-Reasoning

  cl-tm-subst-cong-subst : {σ τ : Γ ⇒ Δ} {t : Tm Δ T} →
                           σ ≅ˢ τ → t [ clT ∣ σ ]cl ≅ᵗᵐ t [ clT ∣ τ ]cl
  cl-tm-subst-cong-subst {σ = σ} {τ} {t} ε =
    begin
      ι⁻¹[ closed-natural clT σ ] (t [ σ ]')
    ≅⟨ ι⁻¹-cong (tm-subst-cong-subst t ε) ⟩
      ι⁻¹[ closed-natural clT σ ] (ι[ ty-subst-cong-subst ε T ] (t [ τ ]'))
    ≅⟨ ι⁻¹-congᵉ-2-1 (closed-subst-eq clT ε) ⟨
      ι⁻¹[ closed-natural clT τ ] (ι⁻¹[ ty-subst-cong-subst ε T ] (ι[ ty-subst-cong-subst ε T ] (t [ τ ]')))
    ≅⟨ ι⁻¹-cong ι-symˡ ⟩
      ι⁻¹[ closed-natural clT τ ] (t [ τ ]') ∎
    where open ≅ᵗᵐ-Reasoning

  cl-tm-subst-cong-tm : {σ : Γ ⇒ Δ} {t s : Tm Δ T} →
                        t ≅ᵗᵐ s → t [ clT ∣ σ ]cl ≅ᵗᵐ s [ clT ∣ σ ]cl
  cl-tm-subst-cong-tm t=s = ι⁻¹-cong (tm-subst-cong-tm _ t=s)

  cl-tm-subst-cong-subst-2-1 : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ : Γ ⇒ Θ} {t : Tm Θ T} →
                               σ2 ⊚ σ1 ≅ˢ τ →
                               t [ clT ∣ σ2 ]cl [ clT ∣ σ1 ]cl ≅ᵗᵐ t [ clT ∣ τ ]cl
  cl-tm-subst-cong-subst-2-1 ε =
    transᵗᵐ (cl-tm-subst-⊚ _) (cl-tm-subst-cong-subst ε)

  cl-tm-subst-cong-subst-2-2 : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ} {t : Tm Θ T} →
                               σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1 →
                               t [ clT ∣ σ2 ]cl [ clT ∣ σ1 ]cl ≅ᵗᵐ t [ clT ∣ τ2 ]cl [ clT ∣ τ1 ]cl
  cl-tm-subst-cong-subst-2-2 ε =
    transᵗᵐ (cl-tm-subst-⊚ _) (transᵗᵐ (cl-tm-subst-cong-subst ε) (symᵗᵐ (cl-tm-subst-⊚ _)))

  ξcl : Tm (Γ ,, T) T
  ξcl = ι⁻¹[ closed-natural clT π ] ξ

_,cl⟨_⟩_ : (Γ ⇒ Δ) → {T : ClosedTy C} → IsClosedNatural T → Tm Γ T → (Γ ⇒ Δ ,, T)
σ ,cl⟨ clT ⟩ t = to-ext-subst _ σ (ι[ closed-natural clT σ ] t)

_/cl⟨_⟩ : {T : ClosedTy C} (t : Tm Γ T) → IsClosedNatural T → (Γ ⇒ Γ ,, T)
_/cl⟨_⟩ {Γ = Γ} t clT = id-subst Γ ,cl⟨ clT ⟩ t

module _ {T : ClosedTy C} (clT : IsClosedNatural T) where
  ,cl-β1 : (σ : Γ ⇒ Δ) (t : Tm Γ T) → π ⊚ (σ ,cl⟨ clT ⟩ t) ≅ˢ σ
  ,cl-β1 σ t = ctx-ext-subst-β₁ _ _

  ,cl-β2 : (σ : Γ ⇒ Δ) (t : Tm Γ T) → (ξcl clT [ clT ∣ σ ,cl⟨ clT ⟩ t ]cl) ≅ᵗᵐ t
  ,cl-β2 σ t =
    begin
      ι⁻¹[ closed-natural clT (σ ,cl⟨ clT ⟩ t) ] ((ι⁻¹[ closed-natural clT π ] ξ) [ σ ,cl⟨ clT ⟩ t ]')
    ≅⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟨
      ι⁻¹[ closed-natural clT (σ ,cl⟨ clT ⟩ t) ] (ι⁻¹[ ty-subst-cong-ty (σ ,cl⟨ clT ⟩ t) (closed-natural clT π) ] (ξ [ σ ,cl⟨ clT ⟩ t ]'))
    ≅⟨ ι⁻¹-cong (ι⁻¹-cong (ctx-ext-subst-β₂ σ _)) ⟩
      ι⁻¹[ closed-natural clT (σ ,cl⟨ clT ⟩ t) ] (ι⁻¹[ ty-subst-cong-ty (σ ,cl⟨ clT ⟩ t) (closed-natural clT π) ]
         (ι[ transᵗʸ (ty-subst-comp T π (σ ,cl⟨ clT ⟩ t))
                     (ty-subst-cong-subst (ctx-ext-subst-β₁ σ (ι[ closed-natural clT σ ] t)) T)
           ] (ι[ closed-natural clT σ ] t)))
    ≅⟨ ι⁻¹-congᵉ-2-2 (closed-⊚ clT π (σ ,cl⟨ clT ⟩ t)) ⟩
      ι⁻¹[ closed-natural clT (π ⊚ (σ ,cl⟨ clT ⟩ t)) ] (ι⁻¹[ ty-subst-comp T π (σ ,cl⟨ clT ⟩ t) ]
         (ι[ transᵗʸ (ty-subst-comp T π (σ ,cl⟨ clT ⟩ t))
                     (ty-subst-cong-subst (ctx-ext-subst-β₁ σ (ι[ closed-natural clT σ ] t)) T)
           ] (ι[ closed-natural clT σ ] t)))
    ≅⟨ ι⁻¹-cong (ι⁻¹-cong ι-trans) ⟩
      ι⁻¹[ closed-natural clT (π ⊚ (σ ,cl⟨ clT ⟩ t)) ] (ι⁻¹[ ty-subst-comp T π (σ ,cl⟨ clT ⟩ t) ] (ι[ ty-subst-comp T π (σ ,cl⟨ clT ⟩ t) ]
         (ι[ ty-subst-cong-subst (ctx-ext-subst-β₁ σ (ι[ closed-natural clT σ ] t)) T
           ] (ι[ closed-natural clT σ ] t))))
    ≅⟨ ι⁻¹-cong ι-symˡ ⟩
      ι⁻¹[ closed-natural clT (π ⊚ (σ ,cl⟨ clT ⟩ t)) ] (ι[ ty-subst-cong-subst (ctx-ext-subst-β₁ σ (ι[ closed-natural clT σ ] t)) T ] (ι[ closed-natural clT σ ] t))
    ≅⟨ ι⁻¹-cong (ι-congᵉ-2-1 (closed-subst-eq clT _)) ⟩
      ι⁻¹[ closed-natural clT (π ⊚ (σ ,cl⟨ clT ⟩ t)) ] (ι[ closed-natural clT (π ⊚ (σ ,cl⟨ clT ⟩ t)) ] t)
    ≅⟨ ι-symˡ ⟩
      t ∎
    where open ≅ᵗᵐ-Reasoning

  ,cl-η : (σ : Γ ⇒ Δ ,, T) → σ ≅ˢ ((π ⊚ σ) ,cl⟨ clT ⟩ (ξcl clT [ clT ∣ σ ]cl))
  ,cl-η σ = transˢ (symˢ (ctx-ext-subst-η σ)) (ctx-ext-subst-cong-tm (π ⊚ σ) (move-ι-right tm-proof))
    where
      open ≅ᵗᵐ-Reasoning
      tm-proof =
        begin
          ι⁻¹[ closed-natural clT (π ⊚ σ) ] (ι⁻¹[ ty-subst-comp T π σ ] (ξ [ σ ]'))
        ≅⟨ ι⁻¹-congᵉ-2-2 (closed-⊚ clT π σ) ⟨
          ι⁻¹[ closed-natural clT σ ] (ι⁻¹[ ty-subst-cong-ty σ (closed-natural clT π) ] (ξ [ σ ]'))
        ≅⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟩
          ι⁻¹[ closed-natural clT σ ] ((ι⁻¹[ closed-natural clT π ] ξ) [ σ ]') ∎

  ,cl-cong-tm : {σ : Γ ⇒ Δ} {t s : Tm Γ T} → t ≅ᵗᵐ s → σ ,cl⟨ clT ⟩ t ≅ˢ σ ,cl⟨ clT ⟩ s
  ,cl-cong-tm 𝒆 = ctx-ext-subst-cong-tm _ (ι-cong 𝒆)

  ,cl-cong-subst : {σ τ : Γ ⇒ Δ} {t : Tm Γ T} → σ ≅ˢ τ → σ ,cl⟨ clT ⟩ t ≅ˢ τ ,cl⟨ clT ⟩ t
  ,cl-cong-subst ε = transˢ (ctx-ext-subst-cong-tm _ (symᵗᵐ (ι-congᵉ-2-1 (closed-subst-eq clT ε)))) (ctx-ext-subst-cong-subst ε _)

  ,cl-cong : {σ τ : Γ ⇒ Δ} {t s : Tm Γ T} → σ ≅ˢ τ → t ≅ᵗᵐ s → σ ,cl⟨ clT ⟩ t ≅ˢ τ ,cl⟨ clT ⟩ s
  ,cl-cong ε 𝒆 = transˢ (,cl-cong-tm 𝒆) (,cl-cong-subst ε)

  /cl-cong : {t t' : Tm Γ T} → t ≅ᵗᵐ t' → (t /cl⟨ clT ⟩) ≅ˢ (t' /cl⟨ clT ⟩)
  /cl-cong = ,cl-cong-tm

  lift-cl-subst : (Γ ⇒ Δ) → (Γ ,, T ⇒ Δ ,, T)
  lift-cl-subst σ = (σ ⊚ π) ,cl⟨ clT ⟩ ξcl clT

  lift-cl-subst-π-commute : {σ : Γ ⇒ Δ} → π ⊚ (lift-cl-subst σ) ≅ˢ σ ⊚ π
  lift-cl-subst-π-commute = ctx-ext-subst-β₁ _ _

  lift-cl-ξcl : {σ : Γ ⇒ Δ} → (ξcl clT) [ clT ∣ lift-cl-subst σ ]cl ≅ᵗᵐ ξcl clT
  lift-cl-ξcl = ,cl-β2 _ _

  lift-cl-subst-⊹ : (σ : Γ ⇒ Δ) → (σ ⊹) ≅ˢ lift-cl-subst σ ⊚ from (,,-cong (closed-natural clT σ))
  eq (lift-cl-subst-⊹ σ) (γ , t) =
    cong (func σ γ ,_) (sym (trans (cong (func (to (closed-natural clT (σ ⊚ π)))) (eq (from-eq (closed-⊚ clT σ π)) t))
                                   (eq (isoˡ (closed-natural clT (σ ⊚ π))) t)))

  ,cl-⊚ : (σ : Δ ⇒ Θ) (t : Tm Δ T) (τ : Γ ⇒ Δ) → (σ ,cl⟨ clT ⟩ t) ⊚ τ ≅ˢ (σ ⊚ τ) ,cl⟨ clT ⟩ (t [ clT ∣ τ ]cl)
  ,cl-⊚ σ t τ =
    begin
      (σ ,cl⟨ clT ⟩ t) ⊚ τ
    ≅⟨ ,cl-η _ ⟩
      (π ⊚ ((σ ,cl⟨ clT ⟩ t) ⊚ τ)) ,cl⟨ clT ⟩
        (ξcl clT [ clT ∣ (σ ,cl⟨ clT ⟩ t) ⊚ τ ]cl)
    ≅⟨ ,cl-cong (transˢ (symˢ ⊚-assoc) (⊚-congˡ (,cl-β1 σ t)))
                (symᵗᵐ (cl-tm-subst-⊚ clT (ξcl clT))) ⟩
      (σ ⊚ τ) ,cl⟨ clT ⟩ ((ξcl clT [ clT ∣ σ ,cl⟨ clT ⟩ t ]cl) [ clT ∣ τ ]cl)
    ≅⟨ ,cl-cong-tm (cl-tm-subst-cong-tm clT (,cl-β2 σ t)) ⟩
      (σ ⊚ τ) ,cl⟨ clT ⟩ (t [ clT ∣ τ ]cl) ∎
    where open ≅ˢ-Reasoning

  /cl-⊚ : (σ : Γ ⇒ Δ) (t : Tm Δ T) → (t /cl⟨ clT ⟩) ⊚ σ ≅ˢ lift-cl-subst σ ⊚ ((t [ clT ∣ σ ]cl) /cl⟨ clT ⟩)
  /cl-⊚ σ t =
    begin
      (id-subst _ ,cl⟨ clT ⟩ t) ⊚ σ
    ≅⟨ ,cl-⊚ _ t σ ⟩
      (id-subst _ ⊚ σ) ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl)
    ≅⟨ ,cl-cong (transˢ (id-subst-unitˡ _) (symˢ (transˢ (transˢ ⊚-assoc (⊚-congʳ (,cl-β1 _ _))) (id-subst-unitʳ _))))
                (symᵗᵐ (,cl-β2 _ _)) ⟩
      (σ ⊚ π ⊚ (id-subst _ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl))) ,cl⟨ clT ⟩
        (ξcl clT [ clT ∣ id-subst _ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl) ]cl)
    ≅⟨ ,cl-⊚ _ _ _ ⟨
      lift-cl-subst σ ⊚ (id-subst _ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl)) ∎
    where open ≅ˢ-Reasoning

  /v-/cl : (t : Tm Δ T) → (t /v) ≅ˢ t /cl⟨ clT ⟩
  /v-/cl t = ctx-ext-subst-cong-tm _ (transᵗᵐ (tm-subst-id t) (ι-congᵉ (symᵉ (closed-id clT))))

module _ {T S : ClosedTy C} (clT : IsClosedNatural T) (clS : IsClosedNatural S) where
  lift-cl-,cl : (σ : Γ ⇒ Δ) (s : Tm (Δ ,, T) S) →
                lift-cl-subst clS σ ⊚ (π ,cl⟨ clS ⟩ (s [ clS ∣ lift-cl-subst clT σ ]cl)) ≅ˢ (π ,cl⟨ clS ⟩ s) ⊚ lift-cl-subst clT σ
  lift-cl-,cl σ s =
    begin
      ((σ ⊚ π) ,cl⟨ clS ⟩ ξcl clS) ⊚ (π ,cl⟨ clS ⟩ (s [ clS ∣ lift-cl-subst clT σ ]cl))
    ≅⟨ ,cl-⊚ clS _ _ _ ⟩
      (σ ⊚ π ⊚ (π ,cl⟨ clS ⟩ (s [ clS ∣ lift-cl-subst clT σ ]cl)))
        ,cl⟨ clS ⟩
      (ξcl clS [ clS ∣ π ,cl⟨ clS ⟩ (s [ clS ∣ lift-cl-subst clT σ ]cl) ]cl)
    ≅⟨ ,cl-cong clS (transˢ ⊚-assoc (⊚-congʳ (,cl-β1 clS _ _))) (,cl-β2 clS _ _) ⟩
      (σ ⊚ π) ,cl⟨ clS ⟩ (s [ clS ∣ lift-cl-subst clT σ ]cl)
    ≅⟨ ,cl-cong-subst clS (lift-cl-subst-π-commute clT) ⟨
      (π ⊚ lift-cl-subst clT σ) ,cl⟨ clS ⟩ (s [ clS ∣ lift-cl-subst clT σ ]cl)
    ≅⟨ ,cl-⊚ clS π s (lift-cl-subst clT σ) ⟨
      (π ,cl⟨ clS ⟩ s) ⊚ lift-cl-subst clT σ ∎
    where open ≅ˢ-Reasoning

_//cl⟨_⟩ : {S : ClosedTy C} {Γ : Ctx C} {T : Ty Γ} (s : Tm (Γ ,, T) S) → IsClosedNatural S →
           (Γ ,, T ⇒ Γ ,, S)
s //cl⟨ clS ⟩ = π ,cl⟨ clS ⟩ s


--------------------------------------------------
-- Since Ty Γ is a groupoid (and not a setoid), naturality of a closed
-- type is in fact structure and not a property. Occasionally we will
-- need to express equivalence of such naturality proofs (e.g. when
-- comparing ⟨ 𝟙 ∣ T ⟩ and T).

record _≅ᶜⁿ_ {A : ClosedTy C} (clA clA' : IsClosedNatural A) : Set₁ where
  field
    closed-natural-eq : (σ : Γ ⇒ Δ) → closed-natural clA σ ≅ᵉ closed-natural clA' σ
open _≅ᶜⁿ_ public

reflᶜⁿ : {A : ClosedTy C} (clA : IsClosedNatural A) → clA ≅ᶜⁿ clA
closed-natural-eq (reflᶜⁿ clA) _ = reflᵉ

symᶜⁿ : {A : ClosedTy C} {clA clA' : IsClosedNatural A} →
        clA ≅ᶜⁿ clA' → clA' ≅ᶜⁿ clA
closed-natural-eq (symᶜⁿ e) σ = symᵉ (closed-natural-eq e σ)

transᶜⁿ : {A : ClosedTy C} {clA1 clA2 clA3 : IsClosedNatural A} →
          clA1 ≅ᶜⁿ clA2 → clA2 ≅ᶜⁿ clA3 → clA1 ≅ᶜⁿ clA3
closed-natural-eq (transᶜⁿ e12 e23) σ = transᵉ (closed-natural-eq e12 σ) (closed-natural-eq e23 σ)

module _ {A : ClosedTy C} {clA clA' : IsClosedNatural A} (e : clA ≅ᶜⁿ clA') where
  cl-tm-subst-cong-cl : {σ : Γ ⇒ Δ} {t : Tm Δ A} →
                        t [ clA ∣ σ ]cl ≅ᵗᵐ t [ clA' ∣ σ ]cl
  cl-tm-subst-cong-cl {σ = σ} = ι⁻¹-congᵉ (closed-natural-eq e σ)

  ξcl-cong-cl : {Γ : Ctx C} → ξcl clA {Γ = Γ} ≅ᵗᵐ ξcl clA'
  ξcl-cong-cl = ι⁻¹-congᵉ (closed-natural-eq e π)

  ,cl-cong-cl : {σ : Γ ⇒ Δ} {t : Tm Γ A} → σ ,cl⟨ clA ⟩ t ≅ˢ σ ,cl⟨ clA' ⟩ t
  ,cl-cong-cl = ctx-ext-subst-cong-tm _ (ι-congᵉ (closed-natural-eq e _))

  /cl-cong-cl : {t : Tm Γ A} → (t /cl⟨ clA ⟩) ≅ˢ (t /cl⟨ clA' ⟩)
  /cl-cong-cl = ,cl-cong-cl

  lift-cl-subst-cong-cl : {σ : Γ ⇒ Δ} → lift-cl-subst clA σ ≅ˢ lift-cl-subst clA' σ
  lift-cl-subst-cong-cl = transˢ ,cl-cong-cl (,cl-cong-tm clA' ξcl-cong-cl)


--------------------------------------------------
-- Definition of equivalence of closed types and some consequences.
-- Note that the notion _≅ᶜⁿ_ is a specialization of _≅ᶜᵗʸ_ where closed-ty-eq is constantly reflᵗʸ.
-- It is however cleaner to separate the two concepts.

-- Naturality amounts to the following diagram to be commutative:
--   A [ σ ]  <-->  B [ σ ]
--      ^              ^
--      |              |
--      v              v
--      A     <-->     B
record _≅ᶜᵗʸ_ {A B : ClosedTy C} (clA : IsClosedNatural A) (clB : IsClosedNatural B) : Set₁ where
  field
    closed-ty-eq : {Γ : Ctx C} → A {Γ} ≅ᵗʸ B
    closed-ty-eq-natural : (σ : Γ ⇒ Δ) →
      transᵗʸ (ty-subst-cong-ty σ closed-ty-eq) (closed-natural clB σ)
        ≅ᵉ
      transᵗʸ (closed-natural clA σ) closed-ty-eq
open _≅ᶜᵗʸ_ public

reflᶜᵗʸ : {A : ClosedTy C} (clA : IsClosedNatural A) → clA ≅ᶜᵗʸ clA
closed-ty-eq (reflᶜᵗʸ clA) = reflᵗʸ
closed-ty-eq-natural (reflᶜᵗʸ clA) σ = transᵉ (transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-refl) reflᵗʸ-unitˡ) (symᵉ reflᵗʸ-unitʳ)

symᶜᵗʸ : {A B : ClosedTy C} {clA : IsClosedNatural A} {clB : IsClosedNatural B} →
         clA ≅ᶜᵗʸ clB → clB ≅ᶜᵗʸ clA
closed-ty-eq (symᶜᵗʸ e) = symᵗʸ (closed-ty-eq e)
closed-ty-eq-natural (symᶜᵗʸ e) σ = transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-sym) (move-symᵗʸ-out (symᵉ (closed-ty-eq-natural e σ)))

transᶜᵗʸ : {A1 A2 A3 : ClosedTy C} {clA1 : IsClosedNatural A1} {clA2 : IsClosedNatural A2} {clA3 : IsClosedNatural A3} →
           clA1 ≅ᶜᵗʸ clA2 → clA2 ≅ᶜᵗʸ clA3 → clA1 ≅ᶜᵗʸ clA3
closed-ty-eq (transᶜᵗʸ e e') = transᵗʸ (closed-ty-eq e) (closed-ty-eq e')
closed-ty-eq-natural (transᶜᵗʸ {clA1 = clA1} {clA2} {clA3} e e') σ =
  begin
    transᵗʸ (ty-subst-cong-ty σ (transᵗʸ (closed-ty-eq e) (closed-ty-eq e'))) (closed-natural clA3 σ)
  ≅⟨ transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-trans) transᵗʸ-assoc ⟩
    transᵗʸ (ty-subst-cong-ty σ (closed-ty-eq e)) (transᵗʸ (ty-subst-cong-ty σ (closed-ty-eq e')) (closed-natural clA3 σ))
  ≅⟨ transᵉ (transᵗʸ-congʳ (closed-ty-eq-natural e' σ)) (symᵉ transᵗʸ-assoc) ⟩
    transᵗʸ (transᵗʸ (ty-subst-cong-ty σ (closed-ty-eq e)) (closed-natural clA2 σ)) (closed-ty-eq e')
  ≅⟨ transᵉ (transᵗʸ-congˡ (closed-ty-eq-natural e σ)) transᵗʸ-assoc ⟩
    transᵗʸ (closed-natural clA1 σ) (transᵗʸ (closed-ty-eq e) (closed-ty-eq e')) ∎
  where open ≅ᵉ-Reasoning

module _ {A B : ClosedTy C} {clA : IsClosedNatural A} {clB : IsClosedNatural B} (e : clA ≅ᶜᵗʸ clB) where
  cl-tm-subst-ι : (σ : Γ ⇒ Δ) (t : Tm Δ B) → (ι[ closed-ty-eq e ] t) [ clA ∣ σ ]cl ≅ᵗᵐ ι[ closed-ty-eq e ] (t [ clB ∣ σ ]cl)
  cl-tm-subst-ι σ t =
    begin
      ι⁻¹[ closed-natural clA σ ] ((ι[ closed-ty-eq e ] t) [ σ ]')
    ≅⟨ ι⁻¹-cong ι-subst-commute ⟨
      ι⁻¹[ closed-natural clA σ ] (ι[ ty-subst-cong-ty σ (closed-ty-eq e) ] (t [ σ ]'))
    ≅⟨ ι-congᵉ-2-2 (to-symᵗʸ-eqˡ (transᵉ (symᵉ (to-symᵗʸ-eqʳ (symᵉ (closed-ty-eq-natural e σ)))) transᵗʸ-assoc)) ⟩
      ι[ closed-ty-eq e ] ι⁻¹[ closed-natural clB σ ] (t [ σ ]') ∎
    where open ≅ᵗᵐ-Reasoning

  ,cl-,,-cong : (σ : Γ ⇒ Δ) (t : Tm Γ A) → from (,,-cong (closed-ty-eq e)) ⊚ (σ ,cl⟨ clA ⟩ t) ≅ˢ σ ,cl⟨ clB ⟩ (ι⁻¹[ closed-ty-eq e ] t)
  ,cl-,,-cong σ t =
    begin
      from (,,-cong (closed-ty-eq e)) ⊚ to-ext-subst A σ (ι[ closed-natural clA σ ] t)
    ≅⟨ ,,-cong-ext-subst (closed-ty-eq e) ⟩
      to-ext-subst B σ (ι⁻¹[ ty-subst-cong-ty σ (closed-ty-eq e) ] (ι[ closed-natural clA σ ] t))
    ≅⟨ ctx-ext-subst-cong-tm σ (ι-congᵉ-2-2 (to-symᵗʸ-eqˡ (transᵉ (symᵉ (to-symᵗʸ-eqʳ (closed-ty-eq-natural e σ))) transᵗʸ-assoc))) ⟩
      to-ext-subst B σ (ι[ closed-natural clB σ ] ι⁻¹[ closed-ty-eq e ] t) ∎
    where open ≅ˢ-Reasoning

  ξcl-,,-cong : {Γ : Ctx C} → ξcl clB {Γ = Γ} [ clB ∣ from (,,-cong (closed-ty-eq e)) ]cl ≅ᵗᵐ ι⁻¹[ closed-ty-eq e ] ξcl clA
  ξcl-,,-cong =
    begin
      ι⁻¹[ closed-natural clB (from (,,-cong (closed-ty-eq e))) ] ((ι⁻¹[ closed-natural clB π ] ξ) [ from (,,-cong (closed-ty-eq e)) ]')
    ≅⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟨
      ι⁻¹[ closed-natural clB (from (,,-cong (closed-ty-eq e))) ] ι⁻¹[ ty-subst-cong-ty (from (,,-cong (closed-ty-eq e))) (closed-natural clB π) ]
           (ξ [ from (,,-cong (closed-ty-eq e)) ]')
    ≅⟨ ι⁻¹-cong (ι⁻¹-cong (,,-cong-ξ (closed-ty-eq e))) ⟩
      ι⁻¹[ closed-natural clB (from (,,-cong (closed-ty-eq e))) ]
        ι⁻¹[ ty-subst-cong-ty (from (,,-cong (closed-ty-eq e))) (closed-natural clB π) ]
        ι[ ty-subst-comp B π (from (,,-cong (closed-ty-eq e))) ]
        ι[ ty-subst-cong-subst (,,-map-π (from (closed-ty-eq e))) B ]
        ι⁻¹[ ty-subst-cong-ty π (closed-ty-eq e) ] ξ
    ≅⟨ ι⁻¹-congᵉ-2-2 (closed-⊚ clB π (from (,,-cong (closed-ty-eq e)))) ⟩
      ι⁻¹[ closed-natural clB (π ⊚ from (,,-cong (closed-ty-eq e))) ]
        ι⁻¹[ ty-subst-comp B π (from (,,-cong (closed-ty-eq e))) ]
        ι[ ty-subst-comp B π (from (,,-cong (closed-ty-eq e))) ]
        ι[ ty-subst-cong-subst (,,-map-π (from (closed-ty-eq e))) B ]
        ι⁻¹[ ty-subst-cong-ty π (closed-ty-eq e) ] ξ
    ≅⟨ ι⁻¹-cong ι-symˡ ⟩
      ι⁻¹[ closed-natural clB (π ⊚ from (,,-cong (closed-ty-eq e))) ]
        ι[ ty-subst-cong-subst (,,-map-π (from (closed-ty-eq e))) B ]
        ι⁻¹[ ty-subst-cong-ty π (closed-ty-eq e) ] ξ
    ≅⟨ ι⁻¹-cong (ι-congᵉ (transᵉ (symᵗʸ-cong ty-subst-cong-subst-sym) symᵗʸ-involutive)) ⟨
      ι⁻¹[ closed-natural clB (π ⊚ from (,,-cong (closed-ty-eq e))) ]
        ι⁻¹[ ty-subst-cong-subst (symˢ (,,-map-π (from (closed-ty-eq e)))) B ]
        ι⁻¹[ ty-subst-cong-ty π (closed-ty-eq e) ] ξ
    ≅⟨ ι⁻¹-congᵉ-2-1 (closed-subst-eq clB (symˢ (,,-map-π (from (closed-ty-eq e))))) ⟩
      ι⁻¹[ closed-natural clB π ] ι⁻¹[ ty-subst-cong-ty π (closed-ty-eq e) ] ξ
    ≅⟨ ι⁻¹-congᵉ-2-2 (closed-ty-eq-natural e π) ⟩
      ι⁻¹[ closed-ty-eq e ] ι⁻¹[ closed-natural clA π ] ξ ∎
    where open ≅ᵗᵐ-Reasoning

  lift-cl-,,-cong-commute : (σ : Γ ⇒ Δ) → from (,,-cong (closed-ty-eq e)) ⊚ lift-cl-subst clA σ ≅ˢ lift-cl-subst clB σ ⊚ from (,,-cong (closed-ty-eq e))
  lift-cl-,,-cong-commute σ =
    begin
      from (,,-cong (closed-ty-eq e)) ⊚ ((σ ⊚ π) ,cl⟨ clA ⟩ ξcl clA)
    ≅⟨ ,cl-,,-cong (σ ⊚ π) (ξcl clA) ⟩
      (σ ⊚ π) ,cl⟨ clB ⟩ (ι⁻¹[ closed-ty-eq e ] ξcl clA)
    ≅⟨ ,cl-cong clB (transˢ ⊚-assoc (⊚-congʳ (,,-map-π (from (closed-ty-eq e)))))
                     ξcl-,,-cong ⟨
        (σ ⊚ π ⊚ from (,,-cong (closed-ty-eq e))) ,cl⟨ clB ⟩ (ξcl clB [ clB ∣ from (,,-cong (closed-ty-eq e)) ]cl)
    ≅⟨ ,cl-⊚ clB (σ ⊚ π) (ξcl clB) (from (,,-cong (closed-ty-eq e))) ⟨
      ((σ ⊚ π) ,cl⟨ clB ⟩ ξcl clB) ⊚ from (,,-cong (closed-ty-eq e)) ∎
    where open ≅ˢ-Reasoning
