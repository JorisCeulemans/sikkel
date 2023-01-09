--------------------------------------------------
-- Sum types
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Sum {C : BaseCategory} where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.Type.Function

private
  variable
    Γ Δ : Ctx C
    T T' S S' : Ty Γ


_⊞_ : Ty Γ → Ty Γ → Ty Γ
T ⊞ S ⟨ x , γ ⟩ = T ⟨ x , γ ⟩ ⊎ S ⟨ x , γ ⟩
T ⊞ S ⟪ f , eγ ⟫ inj₁ t = inj₁ (T ⟪ f , eγ ⟫ t)
T ⊞ S ⟪ f , eγ ⟫ inj₂ s = inj₂ (S ⟪ f , eγ ⟫ s)
ty-cong (T ⊞ S) e {t = inj₁ t} = cong inj₁ (ty-cong T e)
ty-cong (T ⊞ S) e {t = inj₂ s} = cong inj₂ (ty-cong S e)
ty-id (T ⊞ S) {t = inj₁ t} = cong inj₁ (ty-id T)
ty-id (T ⊞ S) {t = inj₂ s} = cong inj₂ (ty-id S)
ty-comp (T ⊞ S) {t = inj₁ t} = cong inj₁ (ty-comp T)
ty-comp (T ⊞ S) {t = inj₂ s} = cong inj₂ (ty-comp S)

⊞-bimap : (T ↣ T') → (S ↣ S') → (T ⊞ S ↣ T' ⊞ S')
func (⊞-bimap η φ) (inj₁ t) = inj₁ (func η t)
func (⊞-bimap η φ) (inj₂ s) = inj₂ (func φ s)
naturality (⊞-bimap η φ) {t = inj₁ t} = cong inj₁ (naturality η)
naturality (⊞-bimap η φ) {t = inj₂ s} = cong inj₂ (naturality φ)

⊞-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⊞ S ≅ᵗʸ T' ⊞ S'
from (⊞-cong T=T' S=S') = ⊞-bimap (from T=T') (from S=S')
to (⊞-cong T=T' S=S') = ⊞-bimap (to T=T') (to S=S')
eq (isoˡ (⊞-cong T=T' S=S')) (inj₁ t) = cong inj₁ (eq (isoˡ T=T') t)
eq (isoˡ (⊞-cong T=T' S=S')) (inj₂ s) = cong inj₂ (eq (isoˡ S=S') s)
eq (isoʳ (⊞-cong T=T' S=S')) (inj₁ t) = cong inj₁ (eq (isoʳ T=T') t)
eq (isoʳ (⊞-cong T=T' S=S')) (inj₂ s) = cong inj₂ (eq (isoʳ S=S') s)

inl : Tm Γ T → Tm Γ (T ⊞ S)
inl t ⟨ x , γ ⟩' = inj₁ (t ⟨ x , γ ⟩')
naturality (inl t) f eγ = cong inj₁ (naturality t f eγ)

inr : Tm Γ S → Tm Γ (T ⊞ S)
inr s ⟨ x , γ ⟩' = inj₂ (s ⟨ x , γ ⟩')
naturality (inr s) f eγ = cong inj₂ (naturality s f eγ)

inl⟨_⟩_ : (S : Ty Γ) (t : Tm Γ T) → Tm Γ (T ⊞ S)
inl⟨ S ⟩ t = inl {S = S} t

inr⟨_⟩_ : (T : Ty Γ) (s : Tm Γ S) → Tm Γ (T ⊞ S)
inr⟨ T ⟩ s = inr {T = T} s

module _ {T S : Ty Γ} where
  inl-cong : {t t' : Tm Γ T} → t ≅ᵗᵐ t' → inl⟨ S ⟩ t ≅ᵗᵐ inl t'
  eq (inl-cong t=t') γ = cong inj₁ (eq t=t' γ)

  inr-cong : {s s' : Tm Γ S} → s ≅ᵗᵐ s' → inr⟨ T ⟩ s ≅ᵗᵐ inr s'
  eq (inr-cong s=s') γ = cong inj₂ (eq s=s' γ)

module _
  {T : Ty Γ} {T' : Ty Γ} {S : Ty Γ} {S' : Ty Γ}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where

  inl-ι : (t : Tm Γ T') → ι[ ⊞-cong T=T' S=S' ] inl t ≅ᵗᵐ inl (ι[ T=T' ] t)
  eq (inl-ι t) _ = refl

  inr-ι : (s : Tm Γ S') → ι[ ⊞-cong T=T' S=S' ] inr s ≅ᵗᵐ inr (ι[ S=S' ] s)
  eq (inr-ι s) _ = refl

module _ {T : Ty Γ} {S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊞-natural : (T ⊞ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊞ (S [ σ ])
  func (from ⊞-natural) = id
  naturality (from ⊞-natural) {t = inj₁ t} = refl
  naturality (from ⊞-natural) {t = inj₂ s} = refl
  func (to ⊞-natural) = id
  naturality (to ⊞-natural) {t = inj₁ t} = refl
  naturality (to ⊞-natural) {t = inj₂ s} = refl
  eq (isoˡ ⊞-natural) _ = refl
  eq (isoʳ ⊞-natural) _ = refl

  inl-natural : (t : Tm Γ T) → (inl t) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inl (t [ σ ]'))
  eq (inl-natural t) _ = refl

  inr-natural : (s : Tm Γ S) → (inr s) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inr (s [ σ ]'))
  eq (inr-natural s) _ = refl

inl-func : Tm Γ (T ⇛ T ⊞ S)
inl-func {T = T} = lam T (ι[ ⊞-natural π ] inl ξ)

inr-func : Tm Γ (S ⇛ T ⊞ S)
inr-func {S = S} = lam S (ι[ ⊞-natural π ] inr ξ)

module _ {A : Ty Γ} {B : Ty Γ} (C : Ty Γ) where
  ⊞-elim : Tm Γ (A ⇛ C) → Tm Γ (B ⇛ C) → Tm Γ (A ⊞ B ⇛ C)
  (⊞-elim f g ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ inj₁ a = f €⟨ _ , _ ⟩ a
  (⊞-elim f g ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ inj₂ b = g €⟨ _ , _ ⟩ b
  naturality (⊞-elim f g ⟨ _ , _ ⟩') {t = inj₁ a} = sym (€-natural f)
  naturality (⊞-elim f g ⟨ _ , _ ⟩') {t = inj₂ b} = sym (€-natural g)
  naturality (⊞-elim f g) _ _ = to-pshfun-eq λ { _ _ (inj₁ a) → refl ; _ _ (inj₂ b) → refl }

  β-⊞-inl : (f : Tm Γ (A ⇛ C)) (g : Tm Γ (B ⇛ C)) (a : Tm Γ A) →
            app (⊞-elim f g) (inl a) ≅ᵗᵐ app f a
  eq (β-⊞-inl f g a) _ = refl

  β-⊞-inr : (f : Tm Γ (A ⇛ C)) (g : Tm Γ (B ⇛ C)) (b : Tm Γ B) →
            app (⊞-elim f g) (inr b) ≅ᵗᵐ app g b
  eq (β-⊞-inr f g b) _ = refl

η-⊞ : {A : Ty Γ} {B : Ty Γ} (t : Tm Γ (A ⊞ B)) →
      t ≅ᵗᵐ app (⊞-elim (A ⊞ B) inl-func inr-func) t
eq (η-⊞ t) γ with t ⟨ _ , γ ⟩'
eq (η-⊞ t) γ | inj₁ a = refl
eq (η-⊞ t) γ | inj₂ b = refl

instance
  sum-closed : {A B : ClosedTy C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
               IsClosedNatural (A ⊞ B)
  closed-natural {{sum-closed}} σ = transᵗʸ (⊞-natural σ) (⊞-cong (closed-natural σ) (closed-natural σ))
