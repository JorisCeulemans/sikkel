--------------------------------------------------
-- Terms
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.Term {C : BaseCategory}  where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Helpers
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextEquivalence
open import Model.CwF-Structure.Type

open BaseCategory C

infix 1 _≅ᵗᵐ_

private
  variable
    x : Ob
    Γ Δ Θ : Ctx C
    T S R : Ty Γ


--------------------------------------------------
-- Definition of terms

record Tm (Γ : Ctx C) (T : Ty Γ) : Set where
  constructor MkTm
  -- no-eta-equality

  field
    term : (x : Ob) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩
    naturality : ∀ {x y} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (f : Hom x y) (eγ : Γ ⟪ f ⟫ γy ≡ γx) →
                 T ⟪ f , eγ ⟫ (term y γy) ≡ term x γx
open Tm public renaming (term to infix 15 _⟨_,_⟩')

private
  variable
    t t' : Tm Γ T
    s s' : Tm Γ S


--------------------------------------------------
-- Equivalence of terms

record _≅ᵗᵐ_ {Γ : Ctx C} {T : Ty Γ} (t s : Tm Γ T) : Set where
  field
    eq : ∀ {x} γ → t ⟨ x , γ ⟩' ≡ s ⟨ x , γ ⟩'
open _≅ᵗᵐ_ public

≅ᵗᵐ-refl : t ≅ᵗᵐ t
eq ≅ᵗᵐ-refl _ = refl

≅ᵗᵐ-sym : t ≅ᵗᵐ t' → t' ≅ᵗᵐ t
eq (≅ᵗᵐ-sym t=t') γ = sym (eq t=t' γ)

≅ᵗᵐ-trans : {t1 t2 t3 : Tm Γ T} → t1 ≅ᵗᵐ t2 → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t3
eq (≅ᵗᵐ-trans t1=t2 t2=t3) γ = trans (eq t1=t2 γ) (eq t2=t3 γ)

module ≅ᵗᵐ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {t s : Tm Γ T} → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  begin_ t=s = t=s

  _≅⟨⟩_ : ∀ (t {s} : Tm Γ T) → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  _ ≅⟨⟩ t=s = t=s

  step-≅ : ∀ (t1 {t2 t3} : Tm Γ T) → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t2 → t1 ≅ᵗᵐ t3
  step-≅ _ t2=t3 t1=t2 = ≅ᵗᵐ-trans t1=t2 t2=t3

  step-≅˘ : ∀ (t1 {t2 t3} : Tm Γ T) → t2 ≅ᵗᵐ t3 → t2 ≅ᵗᵐ t1 → t1 ≅ᵗᵐ t3
  step-≅˘ _ t2=t3 t2=t1 = ≅ᵗᵐ-trans (≅ᵗᵐ-sym t2=t1) t2=t3

  _∎ : ∀ (t : Tm Γ T) → t ≅ᵗᵐ t
  _∎ _ = ≅ᵗᵐ-refl

  syntax step-≅  t1 t2≅t3 t1≅t2 = t1 ≅⟨  t1≅t2 ⟩ t2≅t3
  syntax step-≅˘ t1 t2≅t3 t2≅t1 = t1 ≅˘⟨ t2≅t1 ⟩ t2≅t3

-- Equivalence of terms implies equality of terms (only works because eta-equality for Tm is enabled).
tm-≅-to-≡ : t ≅ᵗᵐ t' → t ≡ t'
tm-≅-to-≡ et = cong₂-d MkTm
  (funext λ _ → funext λ γ → eq et γ)
  (funextI (funextI (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))))


--------------------------------------------------
-- Reindexing maps (cf. Dybjer's internal type theory)

convert-term : (T ↣ S) → Tm Γ T → Tm Γ S
convert-term η t ⟨ x , γ ⟩' = func η (t ⟨ x , γ ⟩')
naturality (convert-term {T = T}{S = S} η t) f eγ =
  begin
    S ⟪ f , eγ ⟫ func η (t ⟨ _ , _ ⟩')
  ≡⟨ naturality η ⟩
    func η (T ⟪ f , eγ ⟫ (t ⟨ _ , _ ⟩'))
  ≡⟨ cong (func η) (naturality t f eγ) ⟩
    func η (t ⟨ _ , _ ⟩') ∎
  where open ≡-Reasoning

convert-term-cong : (η : T ↣ S) → t ≅ᵗᵐ t' →
                    convert-term η t ≅ᵗᵐ convert-term η t'
eq (convert-term-cong η t=t') γ = cong (func η) (eq t=t' γ)

ι[_]_ : T ≅ᵗʸ S → Tm Γ S → Tm Γ T
ι[ T=S ] s = convert-term (to T=S) s

ι-cong : (T=S : T ≅ᵗʸ S) →
         s ≅ᵗᵐ s' → ι[ T=S ] s ≅ᵗᵐ ι[ T=S ] s'
ι-cong T=S s=s' = convert-term-cong (to T=S) s=s'

ι-refl : (t : Tm Γ T) → ι[ ≅ᵗʸ-refl ] t ≅ᵗᵐ t
eq (ι-refl t) _ = refl

ι-symˡ : (T=S : T ≅ᵗʸ S) (s : Tm Γ S) →
         ι[ ≅ᵗʸ-sym T=S ] (ι[ T=S ] s) ≅ᵗᵐ s
eq (ι-symˡ T=S s) γ = eq (isoʳ T=S) (s ⟨ _ , γ ⟩')

ι-symʳ : (T=S : T ≅ᵗʸ S) (t : Tm Γ T) →
         ι[ T=S ] (ι[ ≅ᵗʸ-sym T=S ] t) ≅ᵗᵐ t
eq (ι-symʳ T=S t) γ = eq (isoˡ T=S) (t ⟨ _ , γ ⟩')

ι⁻¹[_]_ : T ≅ᵗʸ S → Tm Γ T → Tm Γ S
ι⁻¹[ T=S ] t = ι[ ≅ᵗʸ-sym T=S ] t

ι⁻¹-cong : (T=S : T ≅ᵗʸ S) →
           t ≅ᵗᵐ t' → ι⁻¹[ T=S ] t ≅ᵗᵐ ι⁻¹[ T=S ] t'
ι⁻¹-cong T=S = ι-cong (≅ᵗʸ-sym T=S)

ι-trans : (T=S : T ≅ᵗʸ S) (S=R : S ≅ᵗʸ R) (r : Tm Γ R) →
          ι[ ≅ᵗʸ-trans T=S S=R ] r ≅ᵗᵐ ι[ T=S ] (ι[ S=R ] r)
eq (ι-trans T=S S=R r) γ = refl


--------------------------------------------------
-- Substitution of terms

_[_]' : Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
t [ σ ]' ⟨ x , δ ⟩' = t ⟨ x , func σ δ ⟩'
naturality (t [ σ ]') f eγ = naturality t f _

tm-subst-cong-tm : (σ : Δ ⇒ Γ) → t ≅ᵗᵐ s → t [ σ ]' ≅ᵗᵐ s [ σ ]'
eq (tm-subst-cong-tm σ t=s) δ = eq t=s (func σ δ)

convert-subst-commute : (σ : Δ ⇒ Γ) (η : T ↣ S) (t : Tm Γ T) →
                        convert-term (ty-subst-map σ η) (t [ σ ]') ≅ᵗᵐ (convert-term η t) [ σ ]'
eq (convert-subst-commute σ η t) δ = refl

ι-subst-commute : (σ : Δ ⇒ Γ) (T=S : T ≅ᵗʸ S) (s : Tm Γ S) →
                  ι[ ty-subst-cong-ty σ T=S ] (s [ σ ]') ≅ᵗᵐ (ι[ T=S ] s) [ σ ]'
ι-subst-commute σ T=S s = convert-subst-commute σ (to T=S) s

tm-subst-cong-subst : {σ τ : Δ ⇒ Γ} (t : Tm Γ T) →
                      (σ=τ : σ ≅ˢ τ) → t [ σ ]' ≅ᵗᵐ ι[ ty-subst-cong-subst σ=τ T ] (t [ τ ]')
eq (tm-subst-cong-subst t σ=τ) δ = sym (naturality t hom-id _)

tm-subst-id : (t : Tm Γ T) → t [ id-subst Γ ]' ≅ᵗᵐ ι[ ty-subst-id T ] t
eq (tm-subst-id t) _ = refl

tm-subst-comp : (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                t [ τ ]' [ σ ]' ≅ᵗᵐ ι[ ty-subst-comp T τ σ ] (t [ τ ⊚ σ ]')
eq (tm-subst-comp t τ σ) _ = refl

-- Nicer syntax for substitutions coming from context equality
ιc[_]'_ : {S : Ty Δ} → (Γ=Δ : Γ ≅ᶜ Δ) → Tm Δ S → Tm Γ (ιc[ Γ=Δ ] S)
ιc[ Γ=Δ ]' s = s [ from Γ=Δ ]'

ιc⁻¹[_]'_ : {T : Ty Γ} → (Γ=Δ : Γ ≅ᶜ Δ) → Tm Γ T → Tm Δ (ιc⁻¹[ Γ=Δ ] T)
ιc⁻¹[ Γ=Δ ]' t = t [ to Γ=Δ ]'
