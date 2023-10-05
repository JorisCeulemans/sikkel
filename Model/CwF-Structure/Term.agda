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
    T S S' R : Ty Γ


--------------------------------------------------
-- Definition of terms

record Tm (Γ : Ctx C) (T : Ty Γ) : Set where
  constructor MkTm
  no-eta-equality

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

reflᵗᵐ : t ≅ᵗᵐ t
eq reflᵗᵐ _ = refl

symᵗᵐ : t ≅ᵗᵐ t' → t' ≅ᵗᵐ t
eq (symᵗᵐ t=t') γ = sym (eq t=t' γ)

transᵗᵐ : {t1 t2 t3 : Tm Γ T} → t1 ≅ᵗᵐ t2 → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t3
eq (transᵗᵐ t1=t2 t2=t3) γ = trans (eq t1=t2 γ) (eq t2=t3 γ)

module ≅ᵗᵐ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {t s : Tm Γ T} → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  begin_ t=s = t=s

  _≅⟨⟩_ : ∀ (t {s} : Tm Γ T) → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  _ ≅⟨⟩ t=s = t=s

  step-≅ : ∀ (t1 {t2 t3} : Tm Γ T) → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t2 → t1 ≅ᵗᵐ t3
  step-≅ _ t2=t3 t1=t2 = transᵗᵐ t1=t2 t2=t3

  step-≅˘ : ∀ (t1 {t2 t3} : Tm Γ T) → t2 ≅ᵗᵐ t3 → t2 ≅ᵗᵐ t1 → t1 ≅ᵗᵐ t3
  step-≅˘ _ t2=t3 t2=t1 = transᵗᵐ (symᵗᵐ t2=t1) t2=t3

  _∎ : ∀ (t : Tm Γ T) → t ≅ᵗᵐ t
  _∎ _ = reflᵗᵐ

  syntax step-≅  t1 t2≅t3 t1≅t2 = t1 ≅⟨  t1≅t2 ⟩ t2≅t3
  syntax step-≅˘ t1 t2≅t3 t2≅t1 = t1 ≅˘⟨ t2≅t1 ⟩ t2≅t3


--------------------------------------------------
-- Reindexing maps (cf. Dybjer's internal type theory)

convert-tm : (T ↣ S) → Tm Γ T → Tm Γ S
convert-tm η t ⟨ x , γ ⟩' = func η (t ⟨ x , γ ⟩')
naturality (convert-tm {T = T}{S = S} η t) f eγ =
  begin
    S ⟪ f , eγ ⟫ func η (t ⟨ _ , _ ⟩')
  ≡⟨ naturality η ⟩
    func η (T ⟪ f , eγ ⟫ (t ⟨ _ , _ ⟩'))
  ≡⟨ cong (func η) (naturality t f eγ) ⟩
    func η (t ⟨ _ , _ ⟩') ∎
  where open ≡-Reasoning

-- Note that instead of the definition below, we could have just
-- written ι[ T=S ] s = convert-tm (to T=S) s. However, the
-- following version enables Agda to infer the type equality proofs
-- when we prove a proposition containing ι[_]_.
ι[_]_ : T ≅ᵗʸ S → Tm Γ S → Tm Γ T
(ι[ T=S ] s) ⟨ x , γ ⟩' = convert-tm (to T=S) s ⟨ x , γ ⟩'
naturality (ι[_]_ {T = T} {S = S} T=S s) f eγ = naturality (convert-tm (to T=S) s) f eγ

ι-convert : {e : T ≅ᵗʸ S} {s : Tm Γ S} → ι[ e ] s ≅ᵗᵐ convert-tm (to e) s
eq ι-convert γ = refl

convert-tm-ι-2-2 : {T T' S R : Ty Γ} {e : T ≅ᵗʸ S} {e' : R ≅ᵗʸ T'} {φ : T ↣ R} {φ' : S ↣ T'} {s : Tm Γ S} →
                   φ ⊙ to e ≅ⁿ to e' ⊙ φ' →
                   convert-tm φ (ι[ e ] s) ≅ᵗᵐ ι[ e' ] convert-tm φ' s
eq (convert-tm-ι-2-2 𝔢) γ = eq 𝔢 _

convert-tm-cong-tm : {φ : T ↣ S} {t t' : Tm Γ T} → t ≅ᵗᵐ t' → convert-tm φ t ≅ᵗᵐ convert-tm φ t'
eq (convert-tm-cong-tm {φ = φ} e) γ = cong (func φ) (eq e γ)

convert-tm-cong-trans : {φ φ' : T ↣ S} {t : Tm Γ T} → φ ≅ⁿ φ' → convert-tm φ t ≅ᵗᵐ convert-tm φ' t
eq (convert-tm-cong-trans 𝔢) γ = eq 𝔢 _

ι-cong : {T=S : T ≅ᵗʸ S} →
         s ≅ᵗᵐ s' → ι[ T=S ] s ≅ᵗᵐ ι[ T=S ] s'
eq (ι-cong {T=S = T=S} s=s') γ = cong (func (to T=S)) (eq s=s' γ)

ι-congᵉ : {e e' : T ≅ᵗʸ S} {t : Tm Γ S} → e ≅ᵉ e' → ι[ e ] t ≅ᵗᵐ ι[ e' ] t
eq (ι-congᵉ 𝑒) γ = eq (to-eq 𝑒) _

ι-refl : {t : Tm Γ T} → ι[ reflᵗʸ ] t ≅ᵗᵐ t
eq ι-refl _ = refl

ι-symˡ : {T=S : T ≅ᵗʸ S} {s : Tm Γ S} →
         ι[ symᵗʸ T=S ] (ι[ T=S ] s) ≅ᵗᵐ s
eq (ι-symˡ {T=S = T=S} {s}) γ = eq (isoʳ T=S) (s ⟨ _ , γ ⟩')

ι-symʳ : {T=S : T ≅ᵗʸ S} {t : Tm Γ T} →
         ι[ T=S ] (ι[ symᵗʸ T=S ] t) ≅ᵗᵐ t
eq (ι-symʳ {T=S = T=S} {t}) γ = eq (isoˡ T=S) (t ⟨ _ , γ ⟩')

ι-trans : {T=S : T ≅ᵗʸ S} {S=R : S ≅ᵗʸ R} {r : Tm Γ R} →
          ι[ transᵗʸ T=S S=R ] r ≅ᵗᵐ ι[ T=S ] (ι[ S=R ] r)
eq ι-trans γ = refl

ι⁻¹[_]_ : T ≅ᵗʸ S → Tm Γ T → Tm Γ S
ι⁻¹[ T=S ] t = ι[ symᵗʸ T=S ] t

ι⁻¹-cong : {T=S : T ≅ᵗʸ S} →
           t ≅ᵗᵐ t' → ι⁻¹[ T=S ] t ≅ᵗᵐ ι⁻¹[ T=S ] t'
ι⁻¹-cong = ι-cong

ι⁻¹-congᵉ : {e e' : T ≅ᵗʸ S} {t : Tm Γ T} → e ≅ᵉ e' → ι⁻¹[ e ] t ≅ᵗᵐ ι⁻¹[ e' ] t
eq (ι⁻¹-congᵉ 𝑒) γ = eq (from-eq 𝑒) _

ι⁻¹-trans : {T=S : T ≅ᵗʸ S} {S=R : S ≅ᵗʸ R} {t : Tm Γ T} →
            ι⁻¹[ transᵗʸ T=S S=R ] t ≅ᵗᵐ ι⁻¹[ S=R ] (ι⁻¹[ T=S ] t)
eq ι⁻¹-trans _ = refl

move-ι-right : {T=S : T ≅ᵗʸ S} {t : Tm Γ T} {s : Tm Γ S} →
               ι⁻¹[ T=S ] t ≅ᵗᵐ s → t ≅ᵗᵐ ι[ T=S ] s
move-ι-right t=s = transᵗᵐ (symᵗᵐ ι-symʳ) (ι-cong t=s)

move-ι-left : {S=T : S ≅ᵗʸ T} {t : Tm Γ T} {s : Tm Γ S} →
              t ≅ᵗᵐ ι⁻¹[ S=T ] s → ι[ S=T ] t ≅ᵗᵐ s
move-ι-left t=s = transᵗᵐ (ι-cong t=s) ι-symʳ

move-ι⁻¹-right : {S=T : S ≅ᵗʸ T} {t : Tm Γ T} {s : Tm Γ S} →
                 ι[ S=T ] t ≅ᵗᵐ s → t ≅ᵗᵐ ι⁻¹[ S=T ] s
move-ι⁻¹-right t=s = transᵗᵐ (symᵗᵐ ι-symˡ) (ι⁻¹-cong t=s)

move-ι⁻¹-left : {T=S : T ≅ᵗʸ S} {t : Tm Γ T} {s : Tm Γ S} →
                t ≅ᵗᵐ ι[ T=S ] s → ι⁻¹[ T=S ] t ≅ᵗᵐ s
move-ι⁻¹-left t=s = transᵗᵐ (ι⁻¹-cong t=s) ι-symˡ

ι-congᵉ-2-1 : {R=S : R ≅ᵗʸ S} {S=T : S ≅ᵗʸ T} {R=T : R ≅ᵗʸ T} {t : Tm Γ T} →
              transᵗʸ R=S S=T ≅ᵉ R=T →
              ι[ R=S ] (ι[ S=T ] t) ≅ᵗᵐ ι[ R=T ] t
ι-congᵉ-2-1 𝑒 = transᵗᵐ (symᵗᵐ ι-trans) (ι-congᵉ 𝑒)

ι⁻¹-congᵉ-2-1 : {R=S : R ≅ᵗʸ S} {S=T : S ≅ᵗʸ T} {R=T : R ≅ᵗʸ T} {r : Tm Γ R} →
                transᵗʸ R=S S=T ≅ᵉ R=T →
                ι⁻¹[ S=T ] (ι⁻¹[ R=S ] r) ≅ᵗᵐ ι⁻¹[ R=T ] r
ι⁻¹-congᵉ-2-1 𝑒 = transᵗᵐ (symᵗᵐ ι⁻¹-trans) (ι⁻¹-congᵉ 𝑒)

ι-congᵉ-2-2 : {R=S : R ≅ᵗʸ S} {S=T : S ≅ᵗʸ T} {R=S' : R ≅ᵗʸ S'} {S'=T : S' ≅ᵗʸ T} {t : Tm Γ T} →
              transᵗʸ R=S S=T ≅ᵉ transᵗʸ R=S' S'=T →
              ι[ R=S ] (ι[ S=T ] t) ≅ᵗᵐ ι[ R=S' ] (ι[ S'=T ] t)
ι-congᵉ-2-2 𝑒 = transᵗᵐ (symᵗᵐ ι-trans) (transᵗᵐ (ι-congᵉ 𝑒) ι-trans)

ι⁻¹-congᵉ-2-2 : {R=S : R ≅ᵗʸ S} {S=T : S ≅ᵗʸ T} {R=S' : R ≅ᵗʸ S'} {S'=T : S' ≅ᵗʸ T} {r : Tm Γ R} →
                transᵗʸ R=S S=T ≅ᵉ transᵗʸ R=S' S'=T →
                ι⁻¹[ S=T ] (ι⁻¹[ R=S ] r) ≅ᵗᵐ ι⁻¹[ S'=T ] (ι⁻¹[ R=S' ] r)
ι⁻¹-congᵉ-2-2 𝑒 = transᵗᵐ (symᵗᵐ ι⁻¹-trans) (transᵗᵐ (ι⁻¹-congᵉ 𝑒) ι⁻¹-trans)


--------------------------------------------------
-- Substitution of terms

_[_]' : Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
t [ σ ]' ⟨ x , δ ⟩' = t ⟨ x , func σ δ ⟩'
naturality (t [ σ ]') f eγ = naturality t f _

tm-subst-cong-tm : (σ : Δ ⇒ Γ) → t ≅ᵗᵐ s → t [ σ ]' ≅ᵗᵐ s [ σ ]'
eq (tm-subst-cong-tm σ t=s) δ = eq t=s (func σ δ)

convert-tm-subst-commute : {σ : Δ ⇒ Γ} {φ : T ↣ S} {t : Tm Γ T} →
                           convert-tm (ty-subst-map σ φ) (t [ σ ]') ≅ᵗᵐ (convert-tm φ t) [ σ ]'
eq convert-tm-subst-commute _ = refl

ι-subst-commute : {σ : Δ ⇒ Γ} {T=S : T ≅ᵗʸ S} {s : Tm Γ S} →
                  ι[ ty-subst-cong-ty σ T=S ] (s [ σ ]') ≅ᵗᵐ (ι[ T=S ] s) [ σ ]'
eq ι-subst-commute _ = refl

ι⁻¹-subst-commute : {σ : Δ ⇒ Γ} {T=S : T ≅ᵗʸ S} {t : Tm Γ T} →
                    ι⁻¹[ ty-subst-cong-ty σ T=S ] (t [ σ ]') ≅ᵗᵐ (ι⁻¹[ T=S ] t) [ σ ]'
eq ι⁻¹-subst-commute _ = refl

tm-subst-cong-subst : {σ τ : Δ ⇒ Γ} (t : Tm Γ T) →
                      (σ=τ : σ ≅ˢ τ) → t [ σ ]' ≅ᵗᵐ ι[ ty-subst-cong-subst σ=τ T ] (t [ τ ]')
eq (tm-subst-cong-subst t σ=τ) δ = sym (naturality t hom-id _)

tm-subst-id : (t : Tm Γ T) → t [ id-subst Γ ]' ≅ᵗᵐ ι[ ty-subst-id T ] t
eq (tm-subst-id t) _ = refl

tm-subst-comp : (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                t [ τ ]' [ σ ]' ≅ᵗᵐ ι[ ty-subst-comp T τ σ ] (t [ τ ⊚ σ ]')
eq (tm-subst-comp t τ σ) _ = refl

tm-subst-cong-subst-2-2 : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ}
                          {T : Ty Θ} (t : Tm Θ T) (ε : σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1) →
                          t [ σ2 ]' [ σ1 ]' ≅ᵗᵐ ι[ ty-subst-cong-subst-2-2 T ε ] (t [ τ2 ]' [ τ1 ]')
eq (tm-subst-cong-subst-2-2 t ε) γ = sym (naturality t _ _)

-- Nicer syntax for substitutions coming from context equality
ιc[_]'_ : {S : Ty Δ} → (Γ=Δ : Γ ≅ᶜ Δ) → Tm Δ S → Tm Γ (ιc[ Γ=Δ ] S)
ιc[ Γ=Δ ]' s = s [ from Γ=Δ ]'

ιc⁻¹[_]'_ : {T : Ty Γ} → (Γ=Δ : Γ ≅ᶜ Δ) → Tm Γ T → Tm Δ (ιc⁻¹[ Γ=Δ ] T)
ιc⁻¹[ Γ=Δ ]' t = t [ to Γ=Δ ]'
