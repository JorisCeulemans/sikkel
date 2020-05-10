open import Categories

module CwF-Structure.SubstitutionSequence {o h} (C : Category {o}{h}) where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts C
open import CwF-Structure.Types C
open import CwF-Structure.Terms C

infixr 5 _∷_

data _⇒⁺_ {ℓ : Level} : Ctx ℓ → Ctx ℓ → Set (o ⊔ h ⊔ lsuc ℓ) where
  _◼ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → Δ ⇒⁺ Γ
  _∷_ : {Δ Γ Θ : Ctx ℓ} (σ : Γ ⇒ Θ) (σs : Δ ⇒⁺ Γ) → Δ ⇒⁺ Θ

fold : {Δ Γ : Ctx ℓ} → Δ ⇒⁺ Γ → Δ ⇒ Γ
fold (σ ◼) = σ
fold (σ ∷ σs) = σ ⊚ fold σs

_⟦_⟧ : {Δ Γ : Ctx ℓ} (T : Ty Γ) (σs : Δ ⇒⁺ Γ) → Ty Δ
T ⟦ σ ◼ ⟧ = T [ σ ]
T ⟦ σ ∷ σs ⟧ = (T [ σ ]) ⟦ σs ⟧

_⟦_⟧' : {Δ Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (σs : Δ ⇒⁺ Γ) → Tm Δ (T ⟦ σs ⟧)
t ⟦ σ ◼ ⟧' = t [ σ ]'
t ⟦ σ ∷ σs ⟧' = (t [ σ ]') ⟦ σs ⟧'

ty-subst-seq-fold : {Δ Γ : Ctx ℓ} (σs : Δ ⇒⁺ Γ) (T : Ty Γ) →
                    T ⟦ σs ⟧ ≅ᵗʸ T [ fold σs ]
ty-subst-seq-fold (σ ◼) T = ≅ᵗʸ-refl
ty-subst-seq-fold (σ ∷ σs) T = ≅ᵗʸ-trans (ty-subst-seq-fold σs (T [ σ ]))
                                         (ty-subst-comp T σ (fold σs))

tm-subst-seq-fold : {Δ Γ : Ctx ℓ} (σs : Δ ⇒⁺ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    t ⟦ σs ⟧' ≅ᵗᵐ ι[ ty-subst-seq-fold σs T ] (t [ fold σs ]')
tm-subst-seq-fold (σ ◼) t = ≅ᵗᵐ-sym (ι-refl _)
tm-subst-seq-fold {Δ = Δ}{Γ} (σ ∷ σs) {T} t =
  begin
    (t [ σ ]') ⟦ σs ⟧'
  ≅⟨ tm-subst-seq-fold σs (t [ σ ]') ⟩
    ι[ ty-subst-seq-fold σs (T [ σ ]) ] ((t [ σ ]') [ fold σs ]')
  ≅⟨ ι-cong (ty-subst-seq-fold σs (T [ σ ])) (tm-subst-comp t σ (fold σs)) ⟩
    ι[ ty-subst-seq-fold σs (T [ σ ]) ] (ι[ ty-subst-comp T σ (fold σs) ] (t [ σ ⊚ fold σs ]'))
  ≅˘⟨ ι-trans (ty-subst-seq-fold σs (T [ σ ])) (ty-subst-comp T σ (fold σs)) (t [ σ ⊚ fold σs ]') ⟩
    ι[ ≅ᵗʸ-trans (ty-subst-seq-fold σs (T [ σ ])) (ty-subst-comp T σ (fold σs)) ] (t [ σ ⊚ fold σs ]') ∎
  where open ≅ᵗᵐ-Reasoning

ty-subst-seq-cong : {Δ Γ : Ctx ℓ} (σs τs : Δ ⇒⁺ Γ) (T : Ty Γ) →
                    fold σs ≅ˢ fold τs →
                    T ⟦ σs ⟧ ≅ᵗʸ T ⟦ τs ⟧
ty-subst-seq-cong σs τs T e =
  begin
    T ⟦ σs ⟧
  ≅⟨ ty-subst-seq-fold σs T ⟩
    T [ fold σs ]
  ≅⟨ ty-subst-cong-subst e T ⟩
    T [ fold τs ]
  ≅˘⟨ ty-subst-seq-fold τs T ⟩
    T ⟦ τs ⟧ ∎
  where open ≅ᵗʸ-Reasoning

{- Probably not necessary anymore since the introduction of ι[_]_
convert-subst : {Δ Γ : Ctx ℓ} (σs τs : Δ ⇒⁺ Γ) {T : Ty Γ} →
                fold σs ≡ fold τs →
                Tm Δ (T ⟦ σs ⟧) → Tm Δ (T ⟦ τs ⟧)
convert-subst {Δ = Δ} σs τs {T} e t = subst (Tm Δ) (ty-subst-seq-cong σs τs T e) t
-}

tm-subst-seq-cong : {Δ Γ : Ctx ℓ} (σs τs : Δ ⇒⁺ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    (e : fold σs ≅ˢ fold τs) →
                    t ⟦ σs ⟧' ≅ᵗᵐ ι[ ty-subst-seq-cong σs τs T e ] (t ⟦ τs ⟧')
tm-subst-seq-cong {Δ = Δ} σs τs {T} t e =
  begin
    t ⟦ σs ⟧'
  ≅⟨ tm-subst-seq-fold σs t ⟩
    ι[ ty-subst-seq-fold σs T ] (t [ fold σs ]')
  ≅⟨ ι-cong (ty-subst-seq-fold σs T) (tm-subst-cong-subst t e) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (t [ fold τs ]'))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-symˡ (ty-subst-seq-fold τs T) (t [ fold τs ]'))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-sym (ty-subst-seq-fold τs T) ] (ι[ ty-subst-seq-fold τs T ] (t [ fold τs ]'))))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-cong (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) (tm-subst-seq-fold τs t))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-sym (ty-subst-seq-fold τs T) ] (t ⟦ τs ⟧')))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-cong (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) (ι-refl _))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-sym (ty-subst-seq-fold τs T) ] (ι[ ≅ᵗʸ-refl ] (t ⟦ τs ⟧'))))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-cong (ty-subst-cong-subst e T) (ι-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl (t ⟦ τs ⟧'))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ ≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl ] (t ⟦ τs ⟧')))
  ≅˘⟨ ι-cong (ty-subst-seq-fold σs T) (ι-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl) (t ⟦ τs ⟧')) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ≅ᵗʸ-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl) ] (t ⟦ τs ⟧'))
  ≅˘⟨ ι-trans (ty-subst-seq-fold σs T) (≅ᵗʸ-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl)) (t ⟦ τs ⟧') ⟩
    ι[ ≅ᵗʸ-trans (ty-subst-seq-fold σs T) (≅ᵗʸ-trans (ty-subst-cong-subst e T) (≅ᵗʸ-trans (≅ᵗʸ-sym (ty-subst-seq-fold τs T)) ≅ᵗʸ-refl)) ] (t ⟦ τs ⟧')
  ≅⟨⟩
    ι[ ty-subst-seq-cong σs τs T e ] (t ⟦ τs ⟧') ∎
  where open ≅ᵗᵐ-Reasoning
{-  subst (Tm Δ) (ty-subst-seq-cong σs τs T e) (t ⟦ σs ⟧')
      ≡⟨⟩
  subst (Tm Δ) (trans (ty-subst-seq-fold σs T) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T)))) (t ⟦ σs ⟧')
      ≡⟨ sym (subst-subst (ty-subst-seq-fold σs T)) ⟩
  subst (Tm Δ) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T)))
    (subst (Tm Δ) (ty-subst-seq-fold σs T) (t ⟦ σs ⟧'))
      ≡⟨ cong (subst (Tm Δ) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T)))) (tm-subst-seq-fold σs t) ⟩
  subst (Tm Δ) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T))) (t [ fold σs ]')
      ≡⟨ sym (subst-subst (cong (T [_]) e)) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T))
    (subst (Tm Δ) (cong (T [_]) e)
    (t [ fold σs ]'))
      ≡⟨ cong (subst (Tm Δ) (sym (ty-subst-seq-fold τs T))) (sym (subst-∘ e)) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T))
    (subst (λ x → Tm Δ (T [ x ])) e
    (t [ fold σs ]'))
      ≡⟨ cong (subst (Tm Δ) (sym (ty-subst-seq-fold τs T))) (cong-d (t [_]') e) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T)) (t [ fold τs ]')
      ≡⟨ cong (subst (Tm Δ) (sym (ty-subst-seq-fold τs T))) (sym (tm-subst-seq-fold τs t)) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T))
    (subst (Tm Δ) (ty-subst-seq-fold τs T)
    (t ⟦ τs ⟧'))
      ≡⟨ subst-sym-subst (ty-subst-seq-fold τs T) ⟩
  t ⟦ τs ⟧' ∎
  where open ≡-Reasoning-}

{-
-- Alternative version (reflexive-transitive closure of _⇒_ instead of transitive closure, which
-- is the same because _⇒_ is already reflexive). Benefit of current version: no id-subst in ⟦_⟧
-- and hence less use of ty-subst-comp and tm-subst-comp.
data _⇒*_ {ℓ : Level} : Ctx ℓ → Ctx ℓ → Set (lsuc ℓ) where
  id : {Γ : Ctx ℓ} → Γ ⇒* Γ
  _∷_ : {Δ Γ Θ : Ctx ℓ} (σ : Γ ⇒ Θ) (σs : Δ ⇒* Γ) → Δ ⇒* Θ

fold : {Δ Γ : Ctx ℓ} → Δ ⇒* Γ → Δ ⇒ Γ
fold id = id-subst _
fold (σ ∷ σs) = σ ⊚ fold σs

_⟦_⟧ : {Δ Γ : Ctx ℓ} (T : Ty Γ) (σs : Δ ⇒* Γ) → Ty Δ
T ⟦ id ⟧ = T
T ⟦ σ ∷ σs ⟧ = (T [ σ ]) ⟦ σs ⟧

_⟦_⟧' : {Δ Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (σs : Δ ⇒* Γ) → Tm Δ (T ⟦ σs ⟧)
t ⟦ id ⟧' = t
t ⟦ σ ∷ σs ⟧' = (t [ σ ]') ⟦ σs ⟧'

ty-subst-seq-fold : {Δ Γ : Ctx ℓ} (σs : Δ ⇒* Γ) (T : Ty Γ) →
                    T ⟦ σs ⟧ ≡ T [ fold σs ]
ty-subst-seq-fold id T = sym (ty-subst-id T)
ty-subst-seq-fold (σ ∷ σs) T = trans (ty-subst-seq-fold σs (T [ σ ]))
                                     (ty-subst-comp T σ (fold σs))

tm-subst-seq-fold : {Δ Γ : Ctx ℓ} (σs : Δ ⇒* Γ) {T : Ty Γ} (t : Tm Γ T) →
                    subst (Tm Δ) (ty-subst-seq-fold σs T) (t ⟦ σs ⟧') ≡ (t [ fold σs ]')
tm-subst-seq-fold {Δ = Δ} id {T} t = trans (cong (subst (Tm Δ) (sym (ty-subst-id T))) (sym (tm-subst-id t)))
                                           (subst-sym-subst (ty-subst-id T))
tm-subst-seq-fold {Δ = Δ} (σ ∷ σs) {T} t = trans (sym (subst-subst (ty-subst-seq-fold σs (T [ σ ]))))
                                                 (trans (cong (subst (Tm Δ) (ty-subst-comp T σ (fold σs))) (tm-subst-seq-fold σs (t [ σ ]')))
                                                        (tm-subst-comp t σ (fold σs)))

ty-subst-seq-cong : {Δ Γ : Ctx ℓ} (σs τs : Δ ⇒* Γ) (T : Ty Γ) →
                    fold σs ≡ fold τs →
                    T ⟦ σs ⟧ ≡ T ⟦ τs ⟧
ty-subst-seq-cong σs τs T e = trans (ty-subst-seq-fold σs T)
                                    (trans (cong (T [_]) e)
                                           (sym (ty-subst-seq-fold τs T)))

convert-subst : {Δ Γ : Ctx ℓ} (σs τs : Δ ⇒* Γ) {T : Ty Γ} →
                fold σs ≡ fold τs →
                Tm Δ (T ⟦ σs ⟧) → Tm Δ (T ⟦ τs ⟧)
convert-subst {Δ = Δ} σs τs {T} e t = subst (Tm Δ) (ty-subst-seq-cong σs τs T e) t

tm-subst-seq-cong : {Δ Γ : Ctx ℓ} (σs τs : Δ ⇒* Γ) {T : Ty Γ} (t : Tm Γ T) →
                    (e : fold σs ≡ fold τs) →
                    subst (Tm Δ) (ty-subst-seq-cong σs τs T e) (t ⟦ σs ⟧') ≡ t ⟦ τs ⟧'
tm-subst-seq-cong {Δ = Δ} σs τs {T} t e =
  subst (Tm Δ) (ty-subst-seq-cong σs τs T e) (t ⟦ σs ⟧')
      ≡⟨⟩
  subst (Tm Δ) (trans (ty-subst-seq-fold σs T) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T)))) (t ⟦ σs ⟧')
      ≡⟨ sym (subst-subst (ty-subst-seq-fold σs T)) ⟩
  subst (Tm Δ) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T)))
    (subst (Tm Δ) (ty-subst-seq-fold σs T) (t ⟦ σs ⟧'))
      ≡⟨ cong (subst (Tm Δ) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T)))) (tm-subst-seq-fold σs t) ⟩
  subst (Tm Δ) (trans (cong (T [_]) e) (sym (ty-subst-seq-fold τs T))) (t [ fold σs ]')
      ≡⟨ sym (subst-subst (cong (T [_]) e)) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T))
    (subst (Tm Δ) (cong (T [_]) e)
    (t [ fold σs ]'))
      ≡⟨ cong (subst (Tm Δ) (sym (ty-subst-seq-fold τs T))) (sym (subst-∘ e)) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T))
    (subst (λ x → Tm Δ (T [ x ])) e
    (t [ fold σs ]'))
      ≡⟨ cong (subst (Tm Δ) (sym (ty-subst-seq-fold τs T))) (cong-d (t [_]') e) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T)) (t [ fold τs ]')
      ≡⟨ cong (subst (Tm Δ) (sym (ty-subst-seq-fold τs T))) (sym (tm-subst-seq-fold τs t)) ⟩
  subst (Tm Δ) (sym (ty-subst-seq-fold τs T))
    (subst (Tm Δ) (ty-subst-seq-fold τs T)
    (t ⟦ τs ⟧'))
      ≡⟨ subst-sym-subst (ty-subst-seq-fold τs T) ⟩
  t ⟦ τs ⟧' ∎
  where open ≡-Reasoning
-}
