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

infix 1 _≅ᶜᵗʸ_


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
    ≅˘⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟩
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
    ≅˘⟨ ι⁻¹-congᵉ-2-1 (closed-subst-eq clT ε) ⟩
      ι⁻¹[ closed-natural clT τ ] (ι⁻¹[ ty-subst-cong-subst ε T ] (ι[ ty-subst-cong-subst ε T ] (t [ τ ]')))
    ≅⟨ ι⁻¹-cong ι-symˡ ⟩
      ι⁻¹[ closed-natural clT τ ] (t [ τ ]') ∎
    where open ≅ᵗᵐ-Reasoning

  cl-tm-subst-cong-tm : {σ : Γ ⇒ Δ} {t s : Tm Δ T} →
                        t ≅ᵗᵐ s → t [ clT ∣ σ ]cl ≅ᵗᵐ s [ clT ∣ σ ]cl
  cl-tm-subst-cong-tm t=s = ι⁻¹-cong (tm-subst-cong-tm _ t=s)

  cl-tm-subst-cong-subst-2-2 : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ} {t : Tm Θ T} →
                               σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1 →
                               t [ clT ∣ σ2 ]cl [ clT ∣ σ1 ]cl ≅ᵗᵐ t [ clT ∣ τ2 ]cl [ clT ∣ τ1 ]cl
  cl-tm-subst-cong-subst-2-2 e-subst =
    transᵗᵐ (cl-tm-subst-⊚ _) (transᵗᵐ (cl-tm-subst-cong-subst e-subst) (symᵗᵐ (cl-tm-subst-⊚ _)))

  ξcl : Tm (Γ ,, T) T
  ξcl = ι⁻¹[ closed-natural clT π ] ξ

_,cl⟨_⟩_ : (Γ ⇒ Δ) → {T : ClosedTy C} → IsClosedNatural T → Tm Γ T → (Γ ⇒ Δ ,, T)
σ ,cl⟨ clT ⟩ t = to-ext-subst _ σ (ι[ closed-natural clT σ ] t)

module _ {T : ClosedTy C} (clT : IsClosedNatural T) where
  ,cl-β1 : (σ : Γ ⇒ Δ) (t : Tm Γ T) → π ⊚ (σ ,cl⟨ clT ⟩ t) ≅ˢ σ
  ,cl-β1 σ t = ctx-ext-subst-β₁ _ _

  ,cl-β2 : (σ : Γ ⇒ Δ) (t : Tm Γ T) → (ξcl clT [ clT ∣ σ ,cl⟨ clT ⟩ t ]cl) ≅ᵗᵐ t
  ,cl-β2 σ t =
    begin
      ι⁻¹[ closed-natural clT (σ ,cl⟨ clT ⟩ t) ] ((ι⁻¹[ closed-natural clT π ] ξ) [ σ ,cl⟨ clT ⟩ t ]')
    ≅˘⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟩
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
        ≅˘⟨ ι⁻¹-congᵉ-2-2 (closed-⊚ clT π σ) ⟩
          ι⁻¹[ closed-natural clT σ ] (ι⁻¹[ ty-subst-cong-ty σ (closed-natural clT π) ] (ξ [ σ ]'))
        ≅⟨ ι⁻¹-cong ι⁻¹-subst-commute ⟩
          ι⁻¹[ closed-natural clT σ ] ((ι⁻¹[ closed-natural clT π ] ξ) [ σ ]') ∎

  ,cl-cong-tm : {σ : Γ ⇒ Δ} {t s : Tm Γ T} → t ≅ᵗᵐ s → σ ,cl⟨ clT ⟩ t ≅ˢ σ ,cl⟨ clT ⟩ s
  ,cl-cong-tm e = ctx-ext-subst-cong-tm _ (ι-cong e)

  ,cl-cong-subst : {σ τ : Γ ⇒ Δ} {t : Tm Γ T} → σ ≅ˢ τ → σ ,cl⟨ clT ⟩ t ≅ˢ τ ,cl⟨ clT ⟩ t
  ,cl-cong-subst e = transˢ (ctx-ext-subst-cong-tm _ (symᵗᵐ (ι-congᵉ-2-1 (closed-subst-eq clT e)))) (ctx-ext-subst-cong-subst e _)

  ,cl-cong : {σ τ : Γ ⇒ Δ} {t s : Tm Γ T} → σ ≅ˢ τ → t ≅ᵗᵐ s → σ ,cl⟨ clT ⟩ t ≅ˢ τ ,cl⟨ clT ⟩ s
  ,cl-cong eσ et = transˢ (,cl-cong-tm et) (,cl-cong-subst eσ)

  lift-cl-subst : (Γ ⇒ Δ) → (Γ ,, T ⇒ Δ ,, T)
  lift-cl-subst σ = (σ ⊚ π) ,cl⟨ clT ⟩ ξcl clT

  lift-cl-subst-π-commute : {σ : Γ ⇒ Δ} → π ⊚ (lift-cl-subst σ) ≅ˢ σ ⊚ π
  lift-cl-subst-π-commute = ctx-ext-subst-β₁ _ _

  lift-cl-subst-⊹ : (σ : Γ ⇒ Δ) → (σ ⊹) ≅ˢ lift-cl-subst σ ⊚ from (,,-cong (closed-natural clT σ))
  eq (lift-cl-subst-⊹ σ) (γ , t) =
    cong (func σ γ ,_) (sym (trans (cong (func (to (closed-natural clT (σ ⊚ π)))) (eq (from-eq (closed-⊚ clT σ π)) t))
                                   (eq (isoˡ (closed-natural clT (σ ⊚ π))) t)))

  ,cl-⊚ : (σ : Δ ⇒ Θ) (t : Tm Δ T) (τ : Γ ⇒ Δ) → (σ ,cl⟨ clT ⟩ t) ⊚ τ ≅ˢ (σ ⊚ τ) ,cl⟨ clT ⟩ (t [ clT ∣ τ ]cl)
  ,cl-⊚ σ t τ = begin
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

  /-⊚ : (σ : Γ ⇒ Δ) (t : Tm Δ T) → (id-subst Δ ,cl⟨ clT ⟩ t) ⊚ σ ≅ˢ lift-cl-subst σ ⊚ (id-subst Γ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl))
  /-⊚ σ t = begin
      (id-subst _ ,cl⟨ clT ⟩ t) ⊚ σ
    ≅⟨ ,cl-⊚ _ t σ ⟩
      (id-subst _ ⊚ σ) ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl)
    ≅⟨ ,cl-cong (transˢ (id-subst-unitˡ _) (symˢ (transˢ (transˢ ⊚-assoc (⊚-congʳ (,cl-β1 _ _))) (id-subst-unitʳ _))))
                (symᵗᵐ (,cl-β2 _ _)) ⟩
      (σ ⊚ π ⊚ (id-subst _ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl))) ,cl⟨ clT ⟩
        (ξcl clT [ clT ∣ id-subst _ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl) ]cl)
    ≅˘⟨ ,cl-⊚ _ _ _ ⟩
      lift-cl-subst σ ⊚ (id-subst _ ,cl⟨ clT ⟩ (t [ clT ∣ σ ]cl)) ∎
    where open ≅ˢ-Reasoning

  /cl : (t : Tm Δ T) → (t /v) ≅ˢ (id-subst Δ ,cl⟨ clT ⟩ t)
  /cl t = ctx-ext-subst-cong-tm _ (transᵗᵐ (tm-subst-id t) (ι-congᵉ (symᵉ (closed-id clT))))


--------------------------------------------------
-- Since Ty Γ is a groupoid (and not a setoid), naturality of a closed
-- type is in fact structure and not a property. Occasionally we will
-- need to express equivalence of such naturality proofs (e.g. when
-- comparing ⟨ 𝟙 ∣ T ⟩ and T).

record _≅ᶜᵗʸ_ {A : ClosedTy C} (clA clA' : IsClosedNatural A) : Set₁ where
  field
    closed-natural-eq : (σ : Γ ⇒ Δ) → closed-natural clA σ ≅ᵉ closed-natural clA' σ
open _≅ᶜᵗʸ_ public

module _ {A : ClosedTy C} {clA clA' : IsClosedNatural A} (e : clA ≅ᶜᵗʸ clA') where
  cl-tm-subst-cl-cong : {σ : Γ ⇒ Δ} {t : Tm Δ A} →
                        t [ clA ∣ σ ]cl ≅ᵗᵐ t [ clA' ∣ σ ]cl
  cl-tm-subst-cl-cong {σ = σ} = ι⁻¹-congᵉ (closed-natural-eq e σ)

  ξcl-cong-cl : {Γ : Ctx C} → ξcl clA {Γ = Γ} ≅ᵗᵐ ξcl clA'
  ξcl-cong-cl = ι⁻¹-congᵉ (closed-natural-eq e π)

  ,cl-cong-cl : {σ : Γ ⇒ Δ} {t : Tm Γ A} → σ ,cl⟨ clA ⟩ t ≅ˢ σ ,cl⟨ clA' ⟩ t
  ,cl-cong-cl = ctx-ext-subst-cong-tm _ (ι-congᵉ (closed-natural-eq e _))
